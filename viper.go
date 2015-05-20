// Tweaked copy of spf13's viper package.  Primary changes are to use
// the 'github/dvln/out' package for output and some adjustments on those
// output statements so are fewer and more "trace" (verbose) debugging
// level to avoid too much noise in regular debug output.
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

	"github.com/dvln/out"
	"github.com/kr/pretty"
	"github.com/mitchellh/mapstructure"
	"github.com/spf13/cast"
	"github.com/spf13/pflag"
	crypt "github.com/xordataexchange/crypt/config"
)

// UseLevel is a type that indicates the level of user should be "at" to use a
// given config key (variable)... meaning they likely don't want to be setting
// or playing with it until they reach a given level (or maybe never at all if
// it is an internal use key/variable setting)
type UseLevel int

// UseLevels available, just integers at this point
const (
	NoviceUser      UseLevel = iota // for novice level users
	StandardUser                    // for "normal" level users
	ExpertUser                      // for expert level users
	AdminUser                       // for admin level users
	InternalUse                     // for internal use primarily, hides it
	RestrictedUse                   // for any (future) restricted global
	UnknownUseLevel                 // in case we have no setting
)

// These fields describe where one can configure a given 'key' (glob variable)
// from so that the calling tool can control which settings are honored.  Of
// course CLI use/setting of a given variable/key must be configured elsewhere
// such as via 'cobra' (the 'cli' commander pkg).
// For 'dvln' needs I've updated the table to also include other ways that
// variables/keys can be set so if you use this in your own library you can
// ignore those levels or trim them out.  The order of evaluation for config
// levels is:
//    Overrides (set via this packages Set() method used after CLI processed)
//    CLI (option given to the command line tool pushed into here via Set())
//    Env (in the users env)
//    Local Config File (in the users tool config file)
//    Remote Key/Val (via a remote key/value store or config)
//    Pkg Singleton Settings (dvln: on an individual "leaf" VCS package)
//    Multi-Package (MPkg) Settings (dvln: on a multi-pkg VCS package)
//    CodeBase Settings (dvln: on a codebase definition VCS package)
//    Default Settings (viper: set via SetDefault(...)
// Note that if keys (globals/variables) have augmented description data added
// such as where they can be set, at which level(s), then settings at that
// level for that variable should not be honored (only valid levels honored).
// This is not fully implemented except for the 'dvln:' focused levels above.
//
// Feature: the VCS Pkg/Codebase related settings in terms of where keys (globs)
//        can be set from, but the builtin 'viper' options don't yet honor
//        these and could be modified to honor them coming up (ie: this way
//        one can use this as a "globals" mechanism and avoid chances of clients
//        overriding some settings via env or config file settings)
const (
	AvailCLI            = 1 << iota // global has a related CLI option available
	AvailEnv                        // global can be set in DVLN_<GLOB>
	AvailCfgFile                    // global can be set in dvln cfg file
	AvailRemote                     // global can be set in remote cfg mechanism
	AvailVCSPkg                     // global can be set on VCS pkg
	AvailVCSMPkg                    // global can be set on VCS multi-pkg pkg
	AvailVCSCodeBasePkg             // global can be set on VCS codebase pkg
	AvailVCSHookPkg                 // global can be set on VCS hook pkg
	AvailVCSPluginPkg               // global can be set on VCS plugin pkg
	AvailDefault                    // global value is coming from default setting

	// Below we have common combinations of the above

	ConstGlobal      = AvailDefault
	BasicGlobal      = AvailEnv | AvailCfgFile | AvailDefault
	CLIGlobal        = AvailCLI | BasicGlobal
	VCSGlobal        = AvailVCSPkg | AvailVCSMPkg | AvailVCSCodeBasePkg | AvailVCSHookPkg | AvailVCSPluginPkg | AvailDefault
	BasicVCSGlobal   = BasicGlobal | VCSGlobal
	FullVCSGlobal    = CLIGlobal | VCSGlobal
	BasicVCSCBGlobal = BasicGlobal | AvailVCSCodeBasePkg
	FullVCSCBGlobal  = CLIGlobal | AvailVCSCodeBasePkg
)

var v *Viper

func init() {
	v = New()
	// If you fork this remove this below line or replace it with your own pfx
	// as this is NOT generic.  It's here because 'dvln' uses init() methods
	// to bootstrap viper settings and viper's is the lowest level init() that
	// we know will run before the init()'s from the various packages using
	// viper... and we want DVLN set for the "general" viper instance early...
	// if we set it in a 'var' in a package or in each init() that bootstraps
	// viper values then it has to be listed in *all* packages that use viper
	// values... that's annoying and likely something folks will forget.  Didn't
	// see a way other than this to insure DVLN is set for all viper users for
	// the singleton viper.
	v.SetEnvPrefix("DVLN")
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
// 5 1/2. the dvln codebase and pkg settings fall into this area
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
	desc     map[string]string
	env      map[string]string
	aliases  map[string]string
	uselevel map[string]UseLevel
	scope    map[string]int
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
	v.desc = make(map[string]string)
	v.uselevel = make(map[string]UseLevel)
	v.scope = make(map[string]int)

	wd, err := os.Getwd()
	if err != nil {
		out.Traceln("Could not add cwd to search paths, error:", err)
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
		absin := AbsPathify(in)
		out.Traceln("adding", absin, "to paths to search")
		if !StringInSlice(absin, v.configPaths) {
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
	if !StringInSlice(provider, SupportedRemoteProviders) {
		return UnsupportedRemoteProviderError(provider)
	}
	if provider != "" && endpoint != "" {
		out.Tracef("adding %s:%s to remote provider list", provider, endpoint)
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
	if !StringInSlice(provider, SupportedRemoteProviders) {
		return UnsupportedRemoteProviderError(provider)
	}
	if provider != "" && endpoint != "" {
		out.Tracef("adding %s:%s to remote provider list", provider, endpoint)
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

// SetPFlags informs viper about CLI flags so it knows what key settings come
// from the command line.  It can be used when viper/cobra/pflags are being used
// in concert *AND* when one wishes to pre-set all defaults manually (if you do
// not wish to do that instead use BindPFlags and not SetPFlags).  The difference
// is that this visits all flags and *only* if they are "Changed" (from the CLI)
// does it identify them as "active" pflags (vs BindPFlags which sets every flag
// in existence into v.pflags[] and uses SetDefault() so vipers default value
// comes from the flags default value setting... to use SetPFlags you should
// have manually set the starting default value for each flag).  So here we only
// put them used CLI's in v.pflags[] and we only use v.Set() to push used CLI
// args in at the v.override[] level (avoids having the app do these Set's).
// Goal: this can tie in later w/support for no args to strings/ints/bools where
// the default would be to take the *options* defined default (thereby putting
// it into play) over the already pre-set default (if/when desired only)
func SetPFlags(flags *pflag.FlagSet) (err error) { return v.SetPFlags(flags) }

// SetPFlags is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetPFlags(flags *pflag.FlagSet) (err error) {
	flags.VisitAll(func(flag *pflag.Flag) {
		if err != nil {
			// an error has been encountered in one of the previous flags
			return
		}
		// If we have a flag and it was used/changed on the CLI:
		if flag.Name != "" && flags.Lookup(flag.Name).Changed {
			flagName := strings.ToLower(flag.Name)
			// Then shove it in as a *used* pflags option
			v.pflags[flagName] = flag
			// And put it in as an override setting
			switch flag.Value.Type() {
			case "int", "int8", "int16", "int32", "int64":
				v.Set(flagName, cast.ToInt(flag.Value.String()))
			case "bool":
				v.Set(flagName, cast.ToBool(flag.Value.String()))
			default:
				v.Set(flagName, flag.Value.String())
			}
		}
	})
	return
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
			val, exists = v.override[key]
			out.Tracef("'%s' found in override (via pflag): %v\n", key, val)
			return flag.Value.String()
		}
	}

	val, exists = v.override[key]
	if exists {
		out.Tracef("'%s' found in override: %v\n", key, val)
		return val
	}

	if v.automaticEnvApplied {
		// even if it hasn't been registered, if automaticEnv is used,
		// check any Get request
		if val = v.getEnv(v.mergeWithEnvPrefix(key)); val != "" {
			out.Tracef("'%s' found in environment: %v\n", key, val)
			return val
		}
	}

	envkey, exists := v.env[key]
	if exists {
		if val = v.getEnv(envkey); val != "" {
			out.Tracef("'%s' found in env: %v\n", envkey, val)
			return val
		}
		// Feature: could put this in a viper testing-only mode, but otherwise
		// it's too verbose so simply disable for now
		//out.Tracef("'%s' was checked in env, not found\n", envkey)
	}

	val, exists = v.config[key]
	if exists {
		out.Tracef("'%s' found in config: %v\n", key, val)
		return val
	}

	val, exists = v.kvstore[key]
	if exists {
		out.Tracef("'%s' found in key/value store: %v\n", key, val)
		return val
	}

	// Feature: need to add in codebase pkg settings to find()

	val, exists = v.defaults[key]
	if exists {
		out.Tracef("'%s' found in defaults: %v\n", key, val)
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
		out.Errorln("Creating circular reference alias:", alias, key, v.realKey(key))
	}
}

func (v *Viper) realKey(key string) string {
	newkey, exists := v.aliases[key]
	if exists {
		out.Tracef("Alias '%s' to '%s'\n", key, newkey)
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

// SetDesc sets the optional description for this key.
func SetDesc(key string, desc string, useLevel UseLevel, cfgScope int) {
	v.SetDesc(key, desc, useLevel, cfgScope)
}

// SetDesc is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetDesc(key string, desc string, useLevel UseLevel, cfgScope int) {
	// If alias passed in, then set the proper default
	key = v.realKey(strings.ToLower(key))
	v.desc[key] = desc
	v.uselevel[key] = useLevel
	v.scope[key] = cfgScope
	// if the config scope is that this should be settable via env setting then
	// lets bind this glob (key) so it is available via the env
	if cfgScope&AvailEnv != 0 {
		v.BindEnv(key)
	}
}

// Desc returns the description, if any, for the given key, if no desc then ""
// for the description, UnknownUseLevel for UseLevel and 0 for where it can
// be set from (ie: nowhere)
func Desc(key string) (string, UseLevel, int) { return v.Desc(key) }

// Desc is same as like named singleton (but drives off given *Viper)
func (v *Viper) Desc(key string) (string, UseLevel, int) {
	// If alias passed in, then set the proper default
	key = v.realKey(strings.ToLower(key))
	if val, ok := v.desc[key]; ok {
		return val, v.uselevel[key], v.scope[key]
	}
	return "", UnknownUseLevel, 0
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
	out.Traceln("Attempting to read in config file:")
	if !StringInSlice(v.getConfigType(), SupportedExts) {
		return UnsupportedConfigError(v.getConfigType())
	}

	fileName := v.getConfigFile()
	fileContents, err := ioutil.ReadFile(fileName)
	if fileName == "" {
		out.Debugln("No config file found to read, skipping (considered normal)")
		return err
	} else if err != nil {
		out.Debugf("Config file \"%s\" read failed\n  Error: %s\n", fileName, err)
		return err
	}
	out.Tracef("---- Config file '%s' contents ----\n%s---- END ----\n", fileName, fileContents)
	v.config = make(map[string]interface{})

	desc := fmt.Sprintf("tool config file \"%s\"", fileName)
	v.marshalReader(bytes.NewReader(fileContents), v.config, desc)
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
func marshalReader(in io.Reader, c map[string]interface{}, desc string) { v.marshalReader(in, c, desc) }
func (v *Viper) marshalReader(in io.Reader, c map[string]interface{}, desc string) {
	marshallConfigReader(in, c, v.getConfigType(), desc)
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
	desc := fmt.Sprintf("remote key/val config from %s", provider.provider)
	v.marshalReader(reader, v.kvstore, desc)
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
	// The full search path is dumped via Trace output already, skip it here
	// out.Traceln("Searching for config in", in)
	for _, ext := range SupportedExts {
		// We know the check works, already know what we're scanning for and
		// since we print out any config file we do find (below), skip this
		// out.Traceln("Checking for", filepath.Join(in, v.configName+"."+ext))
		if b, _ := Exists(filepath.Join(in, v.configName+"."+ext)); b {
			out.Traceln("Found:", filepath.Join(in, v.configName+"."+ext))
			return filepath.Join(in, v.configName+"."+ext)
		}
	}

	return ""
}

// findConfigFile searches all configPaths for any config file.
// Returns the first path that exists (and is a config file)
func (v *Viper) findConfigFile() (string, error) {
	out.Traceln("Searching for config in ", v.configPaths)

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
	out.Traceln("Aliases:")
	out.Trace(pretty.Sprintln(v.aliases))
	out.Traceln("Override:")
	out.Trace(pretty.Sprintln(v.override))
	out.Traceln("PFlags")
	out.Trace(pretty.Sprintln(v.pflags))
	out.Traceln("Env:")
	out.Trace(pretty.Sprintln(v.env))
	out.Traceln("Key/Value Store:")
	out.Trace(pretty.Sprintln(v.kvstore))
	out.Traceln("Config:")
	out.Trace(pretty.Sprintln(v.config))
	out.Traceln("Defaults:")
	out.Trace(pretty.Sprintln(v.defaults))
}

// GetConfig will return a string with available config settings through either
// the env or via the config file so the user can see:
// - what settings are available, what is their current val (at least)
// - optionally show description and a user expertise level recommended
// The verbosity desired ("verbose", "regular", "terse") is passed in
// along with the output "look" desired ("text" or "json").
func GetConfig(lvl string) string { return v.GetConfig(lvl) }

// GetConfig is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetConfig(lvl string) string {
	//eriknow: use verbose and look settings internally in viper, sweet  ;),
	//         need to think, don't want this depending upon my cheesy JSON
	//         formatting library from within 'viper', can return "raw" JSON
	//         format though and we can then pretty up the output (?)
	return ""
	//eriknow: for everything in the desc[key] map we will
	// "do the right thing and either lower case it or merge with env
	// prefix (depending upon what's desired)" and indicate what
	// is available/set/etc and it's current value and such (and
	// long could indicate from where that value came potentially?)
	/*
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
	*/
}

// String implements a stringer for the UseLevel type so we can print out
// a string representations for the user use level setting
func (a UseLevel) String() string {
	uselevel2String := map[UseLevel]string{
		NoviceUser:      "NOVICE",
		StandardUser:    "STANDARD",
		ExpertUser:      "EXPERT",
		AdminUser:       "ADMIN",
		InternalUse:     "INTERNAL",
		RestrictedUse:   "RESTRICTED",
		UnknownUseLevel: "UNKNOWN",
	}
	a = useLevelCheck(a)
	return uselevel2String[a]
}

// UseLevelString2UseLevel takes the string representation of a user/use level
// and returns the UseLevel (Go type) that maps to that string, if mapping
// fails the unknown use level comes back for now
func UseLevelString2UseLevel(s string) UseLevel {
	string2UseLevel := map[string]UseLevel{
		"NOVICE":     NoviceUser,
		"STANDARD":   StandardUser,
		"EXPERT":     ExpertUser,
		"ADMIN":      AdminUser,
		"INTERNAL":   InternalUse,
		"RESTRICTED": RestrictedUse,
		"UNKNOWN":    UnknownUseLevel,
	}
	if _, ok := string2UseLevel[s]; !ok {
		return UnknownUseLevel
	}
	return string2UseLevel[s]
}

// useLevelCheck insures valid user/use level value is provided
func useLevelCheck(useLevel UseLevel) UseLevel {
	switch {
	case useLevel <= NoviceUser:
		return NoviceUser
	case useLevel >= UnknownUseLevel:
		return UnknownUseLevel
	default:
		return UnknownUseLevel
	}
}
