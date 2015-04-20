// Tweaked copy of spf13's viper package.  Primary changes are to
// use the 'dvln/out' package for output and some adjustments on those
// output statements so they are more debugging/trace level statements
// instead of standard info/print output (for dvln only errors with config
// need to be seen, normal functionality should "just work" silently unless
// one is asking for trace level detailed debugging).
//
// Copyright from spf13:
//
// Copyright © 2014 Steve Francia <spf@spf13.com>.
//
// Use of this source code is governed by an MIT-style
// license that can be found in the LICENSE file.

// Viper (aside: use 'cfg' import name for 'dvln' app) is an application
// configuration system, think of it as a smart "global" key/val store.
// It believes that applications can be configured a variety of ways
// via flags, ENVIRONMENT variables, configuration files retrieved
// from the file system, or a remote key/value store.  In the end it
// stores/accesses "keys" case insensitively so case isn't terribly
// important (although env access is done via all upper case)

// For viper config each level or class of setting takes precedence over
// the level/class of setting below it, giving a final configuration once
// they are combined:
// - overrides       : specific calls to viper.Set()
// - flag            : command line flags, eg: --debug|-d
// - env             : environment vars, eg: DVLN_DEBUG
// - config          : config setting, eg: Debug: true (in ~/.dvln/config.json)
// - key/value store : remote key/val store (if configured)
// - default         : configured default setting via viper.SetDefault() API calls
// These are all maintained internally in separate hashes so all settings remain
// very clear at each level/class that has been set.

package viper

import (
	"bytes"
	"fmt"
	"io"
	"io/ioutil"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"time"

	"dvln/lib/out"

	"github.com/kr/pretty"
	"github.com/mitchellh/mapstructure"
	"github.com/spf13/cast"
	"github.com/spf13/pflag"
	crypt "github.com/xordataexchange/crypt/config"
)

var v *Viper

func init() {
	v = New()
}

// UnsupportedConfigError denotes encountering an unsupported
// configuration filetype.
type UnsupportedConfigError string

// Error returns the formatted configuration error.
func (str UnsupportedConfigError) Error() string {
	return fmt.Sprintf("Unsupported Config Type %q", string(str))
}

// UnsupportedRemoteProviderError denotes encountering an unsupported remote
// provider. Currently only Etcd and Consul are
// supported.
type UnsupportedRemoteProviderError string

// Error returns the formatted remote provider error.
func (str UnsupportedRemoteProviderError) Error() string {
	return fmt.Sprintf("Unsupported Remote Provider Type %q", string(str))
}

// RemoteConfigError denotes encountering an error while trying to
// pull the configuration from the remote provider.
type RemoteConfigError string

// Error returns the formatted remote provider error
func (rce RemoteConfigError) Error() string {
	return fmt.Sprintf("Remote Configurations Error: %s", string(rce))
}

// Viper is a prioritized configuration registry. It maintains a set of
// configuration sources, fetches values to populate those, and provides
// them according to the source's priority. The priority of the sources
// is the following:
// 1. overrides
// 2. flags
// 3. env. variables
// 4. config file
// 5. key/value store
// 6. defaults
//
// For example, if values from the following sources were loaded:
//
//  Defaults : {
//  	"secret": "",
//  	"user": "default",
// 	    "endpoint": "https://localhost"
//  }
//  Config : {
//  	"user": "root"
//	    "secret": "defaultsecret"
//  }
//  Env : {
//  	"secret": "somesecretkey"
//  }
//
// The resulting config will have the following values:
//
//	{
//		"secret": "somesecretkey",
//		"user": "root",
//		"endpoint": "https://localhost"
//	}
type Viper struct {
	// Delimiter that separates a list of keys
	// used to access a nested value in one go
	keyDelim string

	// A set of paths to look for the config file in
	configPaths []string

	// A set of remote providers to search for the configuration
	remoteProviders []*remoteProvider

	// Name of file to look for inside the path
	configName string
	configFile string
	configType string
	envPrefix  string

	automaticEnvApplied bool
	envKeyReplacer      *strings.Replacer

	config   map[string]interface{}
	override map[string]interface{}
	defaults map[string]interface{}
	kvstore  map[string]interface{}
	pflags   map[string]*pflag.Flag
	env      map[string]string
	aliases  map[string]string
}

// New returns an initialized Viper instance.
func New() *Viper {
	v := new(Viper)
	v.keyDelim = "."
	v.configName = "config"
	v.config = make(map[string]interface{})
	v.override = make(map[string]interface{})
	v.defaults = make(map[string]interface{})
	v.kvstore = make(map[string]interface{})
	v.pflags = make(map[string]*pflag.Flag)
	v.env = make(map[string]string)
	v.aliases = make(map[string]string)

	wd, err := os.Getwd()
	if err != nil {
		out.Traceln("cfg: Could not add cwd to search paths", err)
	} else {
		v.AddConfigPath(wd)
	}

	return v
}

// Reset is intended for testing, will reset all to default settings.
// In the public interface for the viper package so applications
// can use it in their testing as well.
func Reset() {
	v = New()
	SupportedExts = []string{"json", "toml", "yaml", "yml"}
	SupportedRemoteProviders = []string{"etcd", "consul"}
}

// remoteProvider stores the configuration necessary
// to connect to a remote key/value store.
// Optional secretKeyring to unencrypt encrypted values
// can be provided.
type remoteProvider struct {
	provider      string
	endpoint      string
	path          string
	secretKeyring string
}

// SupportedExts identifies universally supported config file extensions
var SupportedExts = []string{"json", "toml", "yaml", "yml", "properties", "props", "prop"}

// SupportedRemotePrividers identifies Universally supported remote providers
var SupportedRemoteProviders = []string{"etcd", "consul"}

// SetConfigFile explicitly define the path, name and extension of the config
// file viper will use this and not check any of the config paths
func SetConfigFile(in string) { v.SetConfigFile(in) }

// SetConfigFile is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetConfigFile(in string) {
	if in != "" {
		v.configFile = in
	}
}

// SetEnvPrefix defines a prefix that ENVIRONMENT variables will use.
// E.g. if your prefix is "spf", the env registry
// will look for env. variables that start with "SPF_"
func SetEnvPrefix(in string) { v.SetEnvPrefix(in) }

// SetEnvPrefix is same as like named singleton method (drives off given *Viper)
func (v *Viper) SetEnvPrefix(in string) {
	if in != "" {
		v.envPrefix = in
	}
}

func (v *Viper) mergeWithEnvPrefix(in string) string {
	if v.envPrefix != "" {
		return strings.ToUpper(v.envPrefix + "_" + in)
	}

	return strings.ToUpper(in)
}

// TODO: should getEnv logic be moved into find(). Can generalize the use of
// rewriting keys many things, Ex: Get('someKey') -> some_key
// (cammel case to snake case for JSON keys perhaps)

// getEnv is a wrapper around os.Getenv which replaces characters in the original
// key. This allows env vars which have different keys then the config object
// keys
func (v *Viper) getEnv(key string) string {
	if v.envKeyReplacer != nil {
		key = v.envKeyReplacer.Replace(key)
	}
	return os.Getenv(key)
}

// ConfigFileUsed returns the file used to populate the config registry
func ConfigFileUsed() string { return v.ConfigFileUsed() }

// ConfigFileUsed is same as like named singleton (but drives off given *Viper)
func (v *Viper) ConfigFileUsed() string { return v.configFile }

// AddConfigPath adds a path for Viper to search for the config file in.
// Can be called multiple times to define multiple search paths.
func AddConfigPath(in string) { v.AddConfigPath(in) }

// AddConfigPath is same as like named singleton (but drives off given *Viper)
func (v *Viper) AddConfigPath(in string) {
	if in != "" {
		absin := absPathify(in)
		out.Traceln("adding", absin, "to paths to search")
		if !stringInSlice(absin, v.configPaths) {
			v.configPaths = append(v.configPaths, absin)
		}
	}
}

// AddRemoteProvider adds a remote configuration source.
// Remote Providers are searched in the order they are added.
// provider is a string value, "etcd" or "consul" are currently supported.
// endpoint is the url.  etcd requires http://ip:port  consul requires ip:port
// path is the path in the k/v store to retrieve configuration
// To retrieve a config file called myapp.json from /configs/myapp.json
// you should set path to /configs and set config name (SetConfigName()) to
// "myapp"
func AddRemoteProvider(provider, endpoint, path string) error {
	return v.AddRemoteProvider(provider, endpoint, path)
}

// AddRemoteProvider same as like named singleton (but drives off given *Viper)
func (v *Viper) AddRemoteProvider(provider, endpoint, path string) error {
	if !stringInSlice(provider, SupportedRemoteProviders) {
		return UnsupportedRemoteProviderError(provider)
	}
	if provider != "" && endpoint != "" {
		out.Tracef("cfg: adding %s:%s to remote provider list", provider, endpoint)
		rp := &remoteProvider{
			endpoint: endpoint,
			provider: provider,
			path:     path,
		}
		if !v.providerPathExists(rp) {
			v.remoteProviders = append(v.remoteProviders, rp)
		}
	}
	return nil
}

// AddSecureRemoteProvider adds a remote configuration source.
// Secure Remote Providers are searched in the order they are added.
// provider is a string value, "etcd" or "consul" are currently supported.
// endpoint is the url.  etcd requires http://ip:port  consul requires ip:port
// secretkeyring is the filepath to your openpgp secret keyring.  e.g. /etc/secrets/myring.gpg
// path is the path in the k/v store to retrieve configuration
// To retrieve a config file called myapp.json from /configs/myapp.json
// you should set path to /configs and set config name (SetConfigName()) to
// "myapp"
// Secure Remote Providers are implemented with github.com/xordataexchange/crypt
func AddSecureRemoteProvider(provider, endpoint, path, secretkeyring string) error {
	return v.AddSecureRemoteProvider(provider, endpoint, path, secretkeyring)
}

// AddSecureRemoteProvider is same as like named singleton (but drives off
// given *Viper)
func (v *Viper) AddSecureRemoteProvider(provider, endpoint, path, secretkeyring string) error {
	if !stringInSlice(provider, SupportedRemoteProviders) {
		return UnsupportedRemoteProviderError(provider)
	}
	if provider != "" && endpoint != "" {
		out.Tracef("cfg: adding %s:%s to remote provider list", provider, endpoint)
		rp := &remoteProvider{
			endpoint: endpoint,
			provider: provider,
			path:     path,
		}
		if !v.providerPathExists(rp) {
			v.remoteProviders = append(v.remoteProviders, rp)
		}
	}
	return nil
}

func (v *Viper) providerPathExists(p *remoteProvider) bool {
	for _, y := range v.remoteProviders {
		if reflect.DeepEqual(y, p) {
			return true
		}
	}
	return false
}

func (v *Viper) searchMap(source map[string]interface{}, path []string) interface{} {

	if len(path) == 0 {
		return source
	}

	if next, ok := source[path[0]]; ok {
		switch next.(type) {
		case map[string]interface{}:
			// Type assertion is safe here since it is only reached
			// if the type of `next` is the same as the type being asserted
			return v.searchMap(next.(map[string]interface{}), path[1:])
		default:
			return next
		}
	} else {
		return nil
	}
}

// Viper is essentially repository for configurations

// Get can retrieve any value given the key to use
// Get has the behavior of returning the value associated with the first
// place from where it is set. Viper will check in the following order:
// override, flag, env, config file, key/value store, default
//
// Get returns an interface. For a specific value use one of the Get____ methods.
func Get(key string) interface{} { return v.Get(key) }

// Get is same as like named singleton (but drives off given *Viper)
func (v *Viper) Get(key string) interface{} {
	path := strings.Split(key, v.keyDelim)

	val := v.find(strings.ToLower(key))

	if val == nil {
		source := v.find(path[0])
		if source == nil {
			return nil
		}

		if reflect.TypeOf(source).Kind() == reflect.Map {
			val = v.searchMap(cast.ToStringMap(source), path[1:])
		}
	}

	switch val.(type) {
	case bool:
		return cast.ToBool(val)
	case string:
		return cast.ToString(val)
	case int64, int32, int16, int8, int:
		return cast.ToInt(val)
	case float64, float32:
		return cast.ToFloat64(val)
	case time.Time:
		return cast.ToTime(val)
	case time.Duration:
		return cast.ToDuration(val)
	case []string:
		return val
	}
	return val
}

// GetString returns the value associated with the key as a string
func GetString(key string) string { return v.GetString(key) }

// GetString is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetString(key string) string {
	return cast.ToString(v.Get(key))
}

// GetBool returns the value associated with the key asa boolean
func GetBool(key string) bool { return v.GetBool(key) }

// GetBool is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetBool(key string) bool {
	return cast.ToBool(v.Get(key))
}

// GetInt returns the value associated with the key as an integer
func GetInt(key string) int { return v.GetInt(key) }

// GetInt is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetInt(key string) int {
	return cast.ToInt(v.Get(key))
}

// GetFloat64 returns the value associated with the key as a float64
func GetFloat64(key string) float64 { return v.GetFloat64(key) }

// GetFloat64 is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetFloat64(key string) float64 {
	return cast.ToFloat64(v.Get(key))
}

// GetTime returns the value associated with the key as time
func GetTime(key string) time.Time { return v.GetTime(key) }

// GetTime is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetTime(key string) time.Time {
	return cast.ToTime(v.Get(key))
}

// GetDuration returns the value associated with the key as a duration
func GetDuration(key string) time.Duration { return v.GetDuration(key) }

// GetDuration is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetDuration(key string) time.Duration {
	return cast.ToDuration(v.Get(key))
}

// GetStringSlice returns the value associated with the key as a slice
// of strings
func GetStringSlice(key string) []string { return v.GetStringSlice(key) }

// GetStringSlice is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetStringSlice(key string) []string {
	return cast.ToStringSlice(v.Get(key))
}

// GetStringMap returns the value associated with the key as a map of interfaces
func GetStringMap(key string) map[string]interface{} { return v.GetStringMap(key) }

// GetStringMap is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetStringMap(key string) map[string]interface{} {
	return cast.ToStringMap(v.Get(key))
}

// GetStringMapString returns the value associated with the key as a map
// of strings
func GetStringMapString(key string) map[string]string { return v.GetStringMapString(key) }

// GetStringMapString is same as like named singleton (but drives off
// given *Viper)
func (v *Viper) GetStringMapString(key string) map[string]string {
	return cast.ToStringMapString(v.Get(key))
}

// GetSizeInBytes returns the size of the value associated with the given key
// in bytes.
func GetSizeInBytes(key string) uint { return v.GetSizeInBytes(key) }

// GetSizeInBytes is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetSizeInBytes(key string) uint {
	sizeStr := cast.ToString(v.Get(key))
	return parseSizeInBytes(sizeStr)
}

// MarshalKey takes a single key and marshals it into a Struct
func MarshalKey(key string, rawVal interface{}) error { return v.MarshalKey(key, rawVal) }

// MarshalKey is same as like named singleton (but drives off given *Viper)
func (v *Viper) MarshalKey(key string, rawVal interface{}) error {
	return mapstructure.Decode(v.Get(key), rawVal)
}

// Marshal marshals the config into a Struct. Make sure that the tags
// on the fields of the structure are properly set.
func Marshal(rawVal interface{}) error { return v.Marshal(rawVal) }

// Marshal is same as like named singleton (but drives off given *Viper)
func (v *Viper) Marshal(rawVal interface{}) error {
	err := mapstructure.WeakDecode(v.AllSettings(), rawVal)

	if err != nil {
		return err
	}

	v.insensitiviseMaps()

	return nil
}

// BindPFlags finds a full flag set to the configuration, using each flag's long
// name as the config key.
func BindPFlags(flags *pflag.FlagSet) (err error) { return v.BindPFlags(flags) }

// BindPFlags is same as like named singleton (but drives off given *Viper)
func (v *Viper) BindPFlags(flags *pflag.FlagSet) (err error) {
	flags.VisitAll(func(flag *pflag.Flag) {
		if err != nil {
			// an error has been encountered in one of the previous flags
			return
		}

		err = v.BindPFlag(flag.Name, flag)
		switch flag.Value.Type() {
		case "int", "int8", "int16", "int32", "int64":
			v.SetDefault(flag.Name, cast.ToInt(flag.Value.String()))
		case "bool":
			v.SetDefault(flag.Name, cast.ToBool(flag.Value.String()))
		default:
			v.SetDefault(flag.Name, flag.Value.String())
		}
	})
	return
}

// BindPFlag binds a specific key to a flag (as used by cobra)
// Example(where serverCmd is a Cobra instance):
//
//	 serverCmd.Flags().Int("port", 1138, "Port to run Application server on")
//	 Viper.BindPFlag("port", serverCmd.Flags().Lookup("port"))
//
func BindPFlag(key string, flag *pflag.Flag) (err error) { return v.BindPFlag(key, flag) }

// BindPFlag is same as like named singleton (but drives off given *Viper)
func (v *Viper) BindPFlag(key string, flag *pflag.Flag) (err error) {
	if flag == nil {
		return fmt.Errorf("flag for %q is nil", key)
	}
	v.pflags[strings.ToLower(key)] = flag

	switch flag.Value.Type() {
	case "int", "int8", "int16", "int32", "int64":
		SetDefault(key, cast.ToInt(flag.Value.String()))
	case "bool":
		SetDefault(key, cast.ToBool(flag.Value.String()))
	default:
		SetDefault(key, flag.Value.String())
	}
	return nil
}

// BindEnv binds a Viper key to a ENV variable
// ENV variables are case sensitive
// If only a key is provided, it will use the env key matching the key, uppercased.
// EnvPrefix will be used when set when env name is not provided.
func BindEnv(input ...string) (err error) { return v.BindEnv(input...) }

// BindEnv is same as like named singleton (but drives off given *Viper)
func (v *Viper) BindEnv(input ...string) (err error) {
	var key, envkey string
	if len(input) == 0 {
		return fmt.Errorf("BindEnv missing key to bind to")
	}

	key = strings.ToLower(input[0])

	if len(input) == 1 {
		envkey = v.mergeWithEnvPrefix(key)
	} else {
		envkey = input[1]
	}

	v.env[key] = envkey

	return nil
}

// find a given key, return the value
// Viper will check in the following order:
// flag, env, config file, key/value store, default
// Viper will check to see if an alias exists first
func (v *Viper) find(key string) interface{} {
	var val interface{}
	var exists bool

	// if the requested key is an alias, then return the proper key
	key = v.realKey(key)

	// PFlag Override first
	flag, exists := v.pflags[key]
	if exists {
		if flag.Changed {
			out.Traceln("cfg:", key, "found in override (via pflag):", val)
			return flag.Value.String()
		}
	}

	val, exists = v.override[key]
	if exists {
		out.Traceln("cfg:", key, "found in override:", val)
		return val
	}

	if v.automaticEnvApplied {
		// even if it hasn't been registered, if automaticEnv is used,
		// check any Get request
		if val = v.getEnv(v.mergeWithEnvPrefix(key)); val != "" {
			out.Traceln("cfg:", key, "found in environment with val:", val)
			return val
		}
	}

	envkey, exists := v.env[key]
	if exists {
		out.Traceln("cfg:", key, "registered as env var", envkey)
		if val = v.getEnv(envkey); val != "" {
			out.Traceln("cfg:", envkey, "found in environment with val:", val)
			return val
		}
		out.Traceln("cfg:", envkey, "env value unset:")
	}

	val, exists = v.config[key]
	if exists {
		out.Traceln("cfg:", key, "found in config:", val)
		return val
	}

	val, exists = v.kvstore[key]
	if exists {
		out.Traceln("cfg:", key, "found in key/value store:", val)
		return val
	}

	val, exists = v.defaults[key]
	if exists {
		out.Traceln("cfg:", key, "found in defaults:", val)
		return val
	}

	return nil
}

// IsSet checks to see if the key has been set in any of the data locations
func IsSet(key string) bool { return v.IsSet(key) }

// IsSet is same as like named singleton (but drives off given *Viper)
func (v *Viper) IsSet(key string) bool {
	t := v.Get(key)
	return t != nil
}

// AutomaticEnv has viper check ENV variables for all
// keys set in config, default & flags
func AutomaticEnv() { v.AutomaticEnv() }

// AutomaticEnv is same as like named singleton (but drives off given *Viper)
func (v *Viper) AutomaticEnv() {
	v.automaticEnvApplied = true
}

// SetEnvKeyReplacer sets the strings.Replacer on the viper object
// Useful for mapping an environmental variable to a key that does
// not match it.
func SetEnvKeyReplacer(r *strings.Replacer) { v.SetEnvKeyReplacer(r) }

// SetEnvKeyReplacer is same as like named singleton (but drives off
// given *Viper)
func (v *Viper) SetEnvKeyReplacer(r *strings.Replacer) {
	v.envKeyReplacer = r
}

// RegisterAlias is a way to provide another accessor for the same key.
// This enables one to change a name without breaking the application
func RegisterAlias(alias string, key string) { v.RegisterAlias(alias, key) }

// RegisterAlias is same as like named singleton (but drives off given *Viper)
func (v *Viper) RegisterAlias(alias string, key string) {
	v.registerAlias(alias, strings.ToLower(key))
}

func (v *Viper) registerAlias(alias string, key string) {
	alias = strings.ToLower(alias)
	if alias != key && alias != v.realKey(key) {
		_, exists := v.aliases[alias]

		if !exists {
			// if we alias something that exists in one of the maps to another
			// name, we'll never be able to get that value using the original
			// name, so move the config value to the new realkey.
			if val, ok := v.config[alias]; ok {
				delete(v.config, alias)
				v.config[key] = val
			}
			if val, ok := v.kvstore[alias]; ok {
				delete(v.kvstore, alias)
				v.kvstore[key] = val
			}
			if val, ok := v.defaults[alias]; ok {
				delete(v.defaults, alias)
				v.defaults[key] = val
			}
			if val, ok := v.override[alias]; ok {
				delete(v.override, alias)
				v.override[key] = val
			}
			v.aliases[alias] = key
		}
	} else {
		out.Errorln("cfg: Creating circular reference alias:", alias, key, v.realKey(key))
	}
}

func (v *Viper) realKey(key string) string {
	newkey, exists := v.aliases[key]
	if exists {
		out.Traceln("cfg:", "Alias", key, "to", newkey)
		return v.realKey(newkey)
	}
	return key
}

// InConfig checks to see if the given key (or an alias) is in the config file
func InConfig(key string) bool { return v.InConfig(key) }

// InConfig is same as like named singleton (but drives off given *Viper)
func (v *Viper) InConfig(key string) bool {
	// if the requested key is an alias, then return the proper key
	key = v.realKey(key)

	_, exists := v.config[key]
	return exists
}

// SetDefault sets the default value for this key.
// Default only used when no value is provided by the user via flag, config or ENV.
func SetDefault(key string, value interface{}) { v.SetDefault(key, value) }

// SetDefault is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetDefault(key string, value interface{}) {
	// If alias passed in, then set the proper default
	key = v.realKey(strings.ToLower(key))
	v.defaults[key] = value
}

// Set Sets the value for the key in the override regiser.
// Will be used instead of values obtained via
// flags, config file, ENV, default, or key/value store
func Set(key string, value interface{}) { v.Set(key, value) }

// Set is same as like named singleton (but drives off given *Viper)
func (v *Viper) Set(key string, value interface{}) {
	// If alias passed in, then set the proper override
	key = v.realKey(strings.ToLower(key))
	v.override[key] = value
}

// ReadInConfig will result in viper discovering and loading the configuration
// file from disk and key/value stores, searching in one of the defined paths.
func ReadInConfig() error { return v.ReadInConfig() }

// ReadInConfig is same as like named singleton (but drives off given *Viper)
func (v *Viper) ReadInConfig() error {
	out.Traceln("cfg: Attempting to read in config file")
	if !stringInSlice(v.getConfigType(), SupportedExts) {
		return UnsupportedConfigError(v.getConfigType())
	}

	file, err := ioutil.ReadFile(v.getConfigFile())
	if err != nil {
		return err
	}

	v.config = make(map[string]interface{})

	v.marshalReader(bytes.NewReader(file), v.config)
	return nil
}

// ReadRemoteConfig attempts to get configuration from a remote source
// and read it in the remote configuration registry.
func ReadRemoteConfig() error { return v.ReadRemoteConfig() }

// ReadRemoteConfig is same as like named singleton (but drives off given *Viper)
func (v *Viper) ReadRemoteConfig() error {
	err := v.getKeyValueConfig()
	if err != nil {
		return err
	}
	return nil
}

// marshalReader marshalls an io.Reader into a map
func marshalReader(in io.Reader, c map[string]interface{}) { v.marshalReader(in, c) }
func (v *Viper) marshalReader(in io.Reader, c map[string]interface{}) {
	marshallConfigReader(in, c, v.getConfigType())
}

func (v *Viper) insensitiviseMaps() {
	insensitiviseMap(v.config)
	insensitiviseMap(v.defaults)
	insensitiviseMap(v.override)
	insensitiviseMap(v.kvstore)
}

// getKeyValueConfig retrieves the first found remote configuration
func (v *Viper) getKeyValueConfig() error {
	for _, rp := range v.remoteProviders {
		val, err := v.getRemoteConfig(rp)
		if err != nil {
			continue
		}
		v.kvstore = val
		return nil
	}
	return RemoteConfigError("No Files Found")
}

func (v *Viper) getRemoteConfig(provider *remoteProvider) (map[string]interface{}, error) {
	var cm crypt.ConfigManager
	var err error

	if provider.secretKeyring != "" {
		kr, err := os.Open(provider.secretKeyring)
		defer kr.Close()
		if err != nil {
			return nil, err
		}
		if provider.provider == "etcd" {
			cm, err = crypt.NewEtcdConfigManager([]string{provider.endpoint}, kr)
		} else {
			cm, err = crypt.NewConsulConfigManager([]string{provider.endpoint}, kr)
		}
	} else {
		if provider.provider == "etcd" {
			cm, err = crypt.NewStandardEtcdConfigManager([]string{provider.endpoint})
		} else {
			cm, err = crypt.NewStandardConsulConfigManager([]string{provider.endpoint})
		}
	}
	if err != nil {
		return nil, err
	}
	b, err := cm.Get(provider.path)
	if err != nil {
		return nil, err
	}
	reader := bytes.NewReader(b)
	v.marshalReader(reader, v.kvstore)
	return v.kvstore, err
}

// AllKeys returns all keys regardless where they are set
func AllKeys() []string { return v.AllKeys() }

// AllKeys is same as like named singleton (but drives off given *Viper)
func (v *Viper) AllKeys() []string {
	m := map[string]struct{}{}

	for key := range v.defaults {
		m[key] = struct{}{}
	}

	for key := range v.config {
		m[key] = struct{}{}
	}

	for key := range v.kvstore {
		m[key] = struct{}{}
	}

	for key := range v.override {
		m[key] = struct{}{}
	}

	a := []string{}
	for x := range m {
		a = append(a, x)
	}

	return a
}

// AllSettings returns all settings as a map[string]interface{}
func AllSettings() map[string]interface{} { return v.AllSettings() }

// AllSettings is same as like named singleton (but drives off given *Viper)
func (v *Viper) AllSettings() map[string]interface{} {
	m := map[string]interface{}{}
	for _, x := range v.AllKeys() {
		m[x] = v.Get(x)
	}

	return m
}

// SetConfigName sets a name for the config file.
// Does not include extension.
func SetConfigName(in string) { v.SetConfigName(in) }

// SetConfigName is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetConfigName(in string) {
	if in != "" {
		v.configName = in
	}
}

// SetConfigType sets the type of the configuration returned by the
// remote source, e.g. "json".
func SetConfigType(in string) { v.SetConfigType(in) }

// SetConfigType is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetConfigType(in string) {
	if in != "" {
		v.configType = in
	}
}

func (v *Viper) getConfigType() string {
	if v.configType != "" {
		return v.configType
	}

	cf := v.getConfigFile()
	ext := filepath.Ext(cf)

	if len(ext) > 1 {
		return ext[1:]
	}
	return ""
}

func (v *Viper) getConfigFile() string {
	// if explicitly set, then use it
	if v.configFile != "" {
		return v.configFile
	}

	cf, err := v.findConfigFile()
	if err != nil {
		return ""
	}

	v.configFile = cf
	return v.getConfigFile()
}

func (v *Viper) searchInPath(in string) (filename string) {
	out.Debugln("cfg: Searching for config in ", in)
	for _, ext := range SupportedExts {
		out.Debugln("cfg: Checking for", filepath.Join(in, v.configName+"."+ext))
		if b, _ := exists(filepath.Join(in, v.configName+"."+ext)); b {
			out.Debugln("Found: ", filepath.Join(in, v.configName+"."+ext))
			return filepath.Join(in, v.configName+"."+ext)
		}
	}

	return ""
}

// findConfigFile searches all configPaths for any config file.
// Returns the first path that exists (and is a config file)
func (v *Viper) findConfigFile() (string, error) {
	out.Traceln("cfg: Searching for config in ", v.configPaths)

	for _, cp := range v.configPaths {
		file := v.searchInPath(cp)
		if file != "" {
			return file, nil
		}
	}

	// try the current working directory
	wd, _ := os.Getwd()
	file := v.searchInPath(wd)
	if file != "" {
		return file, nil
	}
	return "", fmt.Errorf("config file not found in: %s", v.configPaths)
}

// Debug prints all configuration registries for debugging
// purposes, only prints if showing debug level output currently
func Debug() { v.Debug() }

// Debug is same as like named singleton (but drives off given *Viper)
func (v *Viper) Debug() {
	out.Debugln("Aliases:")
	out.Debug(pretty.Sprintln(v.aliases))
	out.Debugln("Override:")
	out.Debug(pretty.Sprintln(v.override))
	out.Debugln("PFlags")
	out.Debug(pretty.Sprintln(v.pflags))
	out.Debugln("Env:")
	out.Debug(pretty.Sprintln(v.env))
	out.Debugln("Key/Value Store:")
	out.Debug(pretty.Sprintln(v.kvstore))
	out.Debugln("Config:")
	out.Debug(pretty.Sprintln(v.config))
	out.Debugln("Defaults:")
	out.Debug(pretty.Sprintln(v.defaults))
}
