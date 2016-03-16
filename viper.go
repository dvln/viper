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
	"log"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"time"

	"github.com/dvln/api"
	"github.com/dvln/cast"
	"github.com/dvln/fsnotify"
	"github.com/dvln/mapstructure"
	"github.com/dvln/out"
	"github.com/dvln/pflag"
	"github.com/dvln/pretty"
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
	InternalGlobal   = AvailDefault
	BasicGlobal      = AvailEnv | AvailCfgFile | AvailDefault
	CLIGlobal        = AvailCLI | BasicGlobal
	CLIOnlyGlobal    = AvailCLI | AvailDefault
	VCSGlobal        = AvailVCSPkg | AvailVCSMPkg | AvailVCSCodeBasePkg | AvailVCSHookPkg | AvailVCSPluginPkg | AvailDefault
	BasicVCSGlobal   = BasicGlobal | VCSGlobal
	FullVCSGlobal    = CLIGlobal | VCSGlobal
	BasicVCSCBGlobal = BasicGlobal | AvailVCSCodeBasePkg
	FullVCSCBGlobal  = CLIGlobal | AvailVCSCodeBasePkg
)

var v *Viper

// GetSingleton allows one to grab the package global viper instance
func GetSingleton() *Viper {
	return v
}

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

type remoteConfigFactory interface {
	Get(rp RemoteProvider) (io.Reader, error)
	Watch(rp RemoteProvider) (io.Reader, error)
}

// RemoteConfig is optional, see the remote package
var RemoteConfig remoteConfigFactory

// UnsupportedConfigError denotes encountering an unsupported
// configuration filetype.
type UnsupportedConfigError string

// Error returns the formatted configuration error.
func (str UnsupportedConfigError) Error() string {
	return fmt.Sprintf("Unsupported Config Type %q", string(str))
}

// UnsupportedRemoteProviderError denotes encountering an unsupported remote
// provider. Currently only etcd and Consul are supported.
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

// ConfigFileNotFoundError denotes failing to find configuration file.
type ConfigFileNotFoundError struct {
	name, locations string
}

// Returns the formatted configuration error.
func (fnfe ConfigFileNotFoundError) Error() string {
	return fmt.Sprintf("Config File %q Not Found in %q", fnfe.name, fnfe.locations)
}

// Viper is a prioritized configuration registry. It
// maintains a set of configuration sources, fetches
// values to populate those, and provides them according
// to the source's priority.
// The priority of the sources is the following:
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
// 	"endpoint": "https://localhost"
//  }
//  Config : {
//  	"user": "root"
//	"secret": "defaultsecret"
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
	remoteProviders []*defaultRemoteProvider

	// Name of file to look for inside the path
	configName string
	configFile string
	configType string
	envPrefix  string

	automaticEnvApplied bool
	envKeyReplacer      *strings.Replacer

	config         map[string]interface{}
	override       map[string]interface{}
	defaults       map[string]interface{}
	kvstore        map[string]interface{}
	pflags         map[string]FlagValue
	desc           map[string]string
	env            map[string]string
	aliases        map[string]string
	useLevel       map[string]UseLevel
	useScope       map[string]int
	typeByDefValue bool
	onConfigChange func(fsnotify.Event)
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
	v.pflags = make(map[string]FlagValue)
	v.env = make(map[string]string)
	v.aliases = make(map[string]string)
	v.desc = make(map[string]string)
	v.useLevel = make(map[string]UseLevel)
	v.useScope = make(map[string]int)
	v.typeByDefValue = false

	return v
}

// Reset is intended for testing, will reset all to default settings.
// In the public interface for the viper package so applications
// can use it in their testing as well.
func Reset() {
	v = New()
	SupportedExts = []string{"json", "toml", "yaml", "yml", "hcl"}
	SupportedRemoteProviders = []string{"etcd", "consul"}
}

type defaultRemoteProvider struct {
	provider      string
	endpoint      string
	path          string
	secretKeyring string
}

func (rp defaultRemoteProvider) Provider() string {
	return rp.provider
}

func (rp defaultRemoteProvider) Endpoint() string {
	return rp.endpoint
}

func (rp defaultRemoteProvider) Path() string {
	return rp.path
}

func (rp defaultRemoteProvider) SecretKeyring() string {
	return rp.secretKeyring
}

// RemoteProvider stores the configuration necessary
// to connect to a remote key/value store.
// Optional secretKeyring to unencrypt encrypted values
// can be provided.
type RemoteProvider interface {
	Provider() string
	Endpoint() string
	Path() string
	SecretKeyring() string
}

// Universally supported extensions.
var SupportedExts []string = []string{"json", "toml", "yaml", "yml", "properties", "props", "prop", "hcl"}

// SupportedRemotePrividers identifies Universally supported remote providers
var SupportedRemoteProviders = []string{"etcd", "consul"}

func OnConfigChange(run func(in fsnotify.Event)) { v.OnConfigChange(run) }
func (v *Viper) OnConfigChange(run func(in fsnotify.Event)) {
	v.onConfigChange = run
}

func WatchConfig() { v.WatchConfig() }
func (v *Viper) WatchConfig() {
	go func() {
		watcher, err := fsnotify.NewWatcher()
		if err != nil {
			log.Fatal(err)
		}
		defer watcher.Close()

		// we have to watch the entire directory to pick up renames/atomic saves in a cross-platform way
		configFile := filepath.Clean(v.getConfigFile())
		configDir, _ := filepath.Split(configFile)

		done := make(chan bool)
		go func() {
			for {
				select {
				case event := <-watcher.Events:
					// we only care about the config file
					if filepath.Clean(event.Name) == configFile {
						if event.Op&fsnotify.Write == fsnotify.Write || event.Op&fsnotify.Create == fsnotify.Create {
							err := v.ReadInConfig()
							if err != nil {
								log.Println("error:", err)
							}
							v.onConfigChange(event)
						}
					}
				case err := <-watcher.Errors:
					log.Println("error:", err)
				}
			}
		}()

		watcher.Add(configDir)
		<-done
	}()
}

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
		out.Tracef("adding %s:%s to remote provider list", provider, endpoint)
		rp := &defaultRemoteProvider{
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
		out.Tracef("adding %s:%s to remote provider list", provider, endpoint)
		rp := &defaultRemoteProvider{
			endpoint:      endpoint,
			provider:      provider,
			path:          path,
			secretKeyring: secretkeyring,
		}
		if !v.providerPathExists(rp) {
			v.remoteProviders = append(v.remoteProviders, rp)
		}
	}
	return nil
}

func (v *Viper) providerPathExists(p *defaultRemoteProvider) bool {
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

	var ok bool
	var next interface{}
	for k, v := range source {
		if strings.ToLower(k) == strings.ToLower(path[0]) {
			ok = true
			next = v
			break
		}
	}

	if ok {
		switch next.(type) {
		case map[interface{}]interface{}:
			return v.searchMap(cast.ToStringMap(next), path[1:])
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

// SetTypeByDefaultValue enables or disables the inference of a key value's
// type when the Get function is used based upon a key's default value as
// opposed to the value returned based on the normal fetch logic.
//
// For example, if a key has a default value of []string{} and the same key
// is set via an environment variable to "a b c", a call to the Get function
// would return a string slice for the key if the key's type is inferred by
// the default value and the Get function would return:
//
//   []string {"a", "b", "c"}
//
// Otherwise the Get function would return:
//
//   "a b c"
func SetTypeByDefaultValue(enable bool) { v.SetTypeByDefaultValue(enable) }
func (v *Viper) SetTypeByDefaultValue(enable bool) {
	v.typeByDefValue = enable
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

	lcaseKey := strings.ToLower(key)
	val := v.find(lcaseKey)

	if val == nil {
		source := v.find(strings.ToLower(path[0]))
		if source != nil {
			if reflect.TypeOf(source).Kind() == reflect.Map {
				val = v.searchMap(cast.ToStringMap(source), path[1:])
			}
		}
	}

	// if no other value is returned and a flag does exist for the value,
	// get the flag's value even if the flag's value has not changed
	if val == nil {
		if flag, exists := v.pflags[lcaseKey]; exists {
			out.Traceln(key, "get pflag default", val)
			switch flag.ValueType() {
			case "int", "int8", "int16", "int32", "int64":
				val = cast.ToInt(flag.ValueString())
			case "bool":
				val = cast.ToBool(flag.ValueString())
			default:
				val = flag.ValueString()
			}
		}
	}

	if val == nil {
		return nil
	}

	var valType interface{}
	if !v.typeByDefValue {
		valType = val
	} else {
		defVal, defExists := v.defaults[lcaseKey]
		if defExists {
			valType = defVal
		} else {
			valType = val
		}
	}

	switch valType.(type) {
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
		return cast.ToStringSlice(val)
	}
	return val
}

// Returns new Viper instance representing a sub tree of this instance
func Sub(key string) *Viper { return v.Sub(key) }
func (v *Viper) Sub(key string) *Viper {
	subv := New()
	data := v.Get(key)
	if reflect.TypeOf(data).Kind() == reflect.Map {
		subv.config = cast.ToStringMap(data)
		return subv
	} else {
		return nil
	}
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

// Returns the value associated with the key as a map to a slice of strings.
func GetStringMapStringSlice(key string) map[string][]string { return v.GetStringMapStringSlice(key) }
func (v *Viper) GetStringMapStringSlice(key string) map[string][]string {
	return cast.ToStringMapStringSlice(v.Get(key))
}

// GetSizeInBytes returns the size of the value associated with the given key
// in bytes.
func GetSizeInBytes(key string) uint { return v.GetSizeInBytes(key) }

// GetSizeInBytes is same as like named singleton (but drives off given *Viper)
func (v *Viper) GetSizeInBytes(key string) uint {
	sizeStr := cast.ToString(v.Get(key))
	return parseSizeInBytes(sizeStr)
}

// UnmarshalKey takes a single key and unmarshals it into a Struct
func UnmarshalKey(key string, rawVal interface{}) error { return v.UnmarshalKey(key, rawVal) }
func (v *Viper) UnmarshalKey(key string, rawVal interface{}) error {
	return mapstructure.Decode(v.Get(key), rawVal)
}

// Unmarshal unmarshals the config into a Struct. Make sure that the tags
// on the fields of the structure are properly set.
func Unmarshal(rawVal interface{}) error { return v.Unmarshal(rawVal) }
func (v *Viper) Unmarshal(rawVal interface{}) error {
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
// put the used CLI's in v.pflags[] and we only use v.Set() to push CLI used
// args in at the v.override[] level (avoids having the app do these Set's).
// Goal: this can tie in later w/support for no args to strings/ints/bools where
// the default would be to take the *options* defined default (thereby putting
// it into play) over the already pre-set default (if/when desired only)
func SetPFlags(flags *pflag.FlagSet) (err error) { return v.SetPFlags(flags) }

// SetPFlags is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetPFlags(flags *pflag.FlagSet) (err error) {
	//flags.VisitAll(func(flag FlagValue) {
	flags.VisitAll(func(flag *pflag.Flag) {

		if err != nil {
			// an error has been encountered in one of the previous flags
			return
		}
		// If we have a flag and it was used/changed on the CLI:
		if flag.Name != "" && flags.Lookup(flag.Name).Changed {
			flagName := strings.ToLower(flag.Name)
			// Then shove it in as a *used* pflags option

			var flagVal pflagValue
			flagVal.flag = flag
			v.pflags[flagName] = flagVal
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

// A wrapper around mapstructure.Decode that mimics the WeakDecode functionality
// while erroring on non existing vals in the destination struct
func weakDecodeExact(input, output interface{}) error {
	config := &mapstructure.DecoderConfig{
		ErrorUnused:      true,
		Metadata:         nil,
		Result:           output,
		WeaklyTypedInput: true,
	}

	decoder, err := mapstructure.NewDecoder(config)
	if err != nil {
		return err
	}
	return decoder.Decode(input)
}

// Unmarshals the config into a Struct, erroring if a field is non-existant
// in the destination struct
func (v *Viper) UnmarshalExact(rawVal interface{}) error {
	err := weakDecodeExact(v.AllSettings(), rawVal)

	if err != nil {
		return err
	}

	v.insensitiviseMaps()

	return nil
}

// BindPFlags finds a full flag set to the configuration, using each flag's long
// Bind a full flag set to the configuration, using each flag's long
// name as the config key.
func BindPFlags(flags *pflag.FlagSet) (err error) { return v.BindPFlags(flags) }

// BindPFlags is same as like named singleton (but drives off given *Viper)
func (v *Viper) BindPFlags(flags *pflag.FlagSet) (err error) {
	return v.BindFlagValues(pflagValueSet{flags})
}

// ClearPFlag is a bit of a hack, used to be replace but was having issues so
// now it's a simple mechanism to clear viper's knowledge of a command line
// flag so that an override can override a command line setting (the way viper
// works is that if pflags has a flag set and a Set() has been called it'll
// actually prefer the pflag setting, not the override setting).  If you want
// it to prefer the Set() override setting you can use this, typically only
// used if one is using SetPflags() above.
func ClearPFlag(key string) { v.ClearPFlag(key) }

// ClearPFlag is same as like named singleton (but drives off given *Viper)
func (v *Viper) ClearPFlag(key string) {
	if key == "" {
		return
	}
	key = strings.ToLower(key)
	_, exists := v.pflags[key]
	if exists {
		delete(v.pflags, key)
	}
}

// BindPFlag binds a specific key to a pflag (as used by cobra)
// Example(where serverCmd is a Cobra instance):
//
//	 serverCmd.Flags().Int("port", 1138, "Port to run Application server on")
//	 Viper.BindPFlag("port", serverCmd.Flags().Lookup("port"))
//
func BindPFlag(key string, flag *pflag.Flag) (err error) { return v.BindPFlag(key, flag) }

// BindPFlag is same as like named singleton (but drives off given *Viper)
func (v *Viper) BindPFlag(key string, flag *pflag.Flag) (err error) {
	return v.BindFlagValue(key, pflagValue{flag})
}

// Bind a full FlagValue set to the configuration, using each flag's long
// name as the config key.
func BindFlagValues(flags FlagValueSet) (err error) { return v.BindFlagValues(flags) }
func (v *Viper) BindFlagValues(flags FlagValueSet) (err error) {
	flags.VisitAll(func(flag FlagValue) {
		if err = v.BindFlagValue(flag.Name(), flag); err != nil {
			return
		}
	})
	return nil
}

// Bind a specific key to a FlagValue.
// Example(where serverCmd is a Cobra instance):
//
//	 serverCmd.Flags().Int("port", 1138, "Port to run Application server on")
//	 Viper.BindFlagValue("port", serverCmd.Flags().Lookup("port"))
//
func BindFlagValue(key string, flag FlagValue) (err error) { return v.BindFlagValue(key, flag) }
func (v *Viper) BindFlagValue(key string, flag FlagValue) (err error) {
	if flag == nil {
		return fmt.Errorf("flag for %q is nil", key)
	}
	v.pflags[strings.ToLower(key)] = flag
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

	if exists && flag.HasChanged() {
		out.Traceln(key, "found in override (via pflag):", flag.ValueString())
		switch flag.ValueType() {
		case "int", "int8", "int16", "int32", "int64":
			return cast.ToInt(flag.ValueString())
		case "bool":
			return cast.ToBool(flag.ValueString())
		default:
			return flag.ValueString()
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

	// Test for nested config parameter
	if strings.Contains(key, v.keyDelim) {
		path := strings.Split(key, v.keyDelim)

		source := v.find(path[0])
		if source != nil {
			if reflect.TypeOf(source).Kind() == reflect.Map {
				val := v.searchMap(cast.ToStringMap(source), path[1:])
				out.Traceln(key, "found in nested config:", val)
				return val
			}
		}
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
	path := strings.Split(key, v.keyDelim)

	lcaseKey := strings.ToLower(key)
	val := v.find(lcaseKey)

	if val == nil {
		source := v.find(strings.ToLower(path[0]))
		if source != nil {
			if reflect.TypeOf(source).Kind() == reflect.Map {
				val = v.searchMap(cast.ToStringMap(source), path[1:])
			}
		}
	}

	return val != nil
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
func SetDesc(key string, desc string, useLevel UseLevel, useScope int) {
	v.SetDesc(key, desc, useLevel, useScope)
}

// SetDesc is same as like named singleton (but drives off given *Viper)
func (v *Viper) SetDesc(key string, desc string, useLevel UseLevel, useScope int) {
	// If alias passed in, then set the proper default
	key = v.realKey(strings.ToLower(key))
	v.desc[key] = desc
	v.useLevel[key] = useLevel
	v.useScope[key] = useScope
	// if the config scope is that this should be settable via env setting then
	// lets bind this glob (key) so it is available via the env
	if useScope&AvailEnv != 0 {
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
		return val, v.useLevel[key], v.useScope[key]
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
	if !stringInSlice(v.getConfigType(), SupportedExts) {
		return UnsupportedConfigError(v.getConfigType())
	}

	file, err := ioutil.ReadFile(v.getConfigFile())
	if err != nil {
		return err
	}

	v.config = make(map[string]interface{})

	return v.unmarshalReader(bytes.NewReader(file), v.config)
}

// MergeInConfig merges a new configuration with an existing config.
func MergeInConfig() error { return v.MergeInConfig() }
func (v *Viper) MergeInConfig() error {
	out.Traceln("Attempting to merge in config file")
	if !stringInSlice(v.getConfigType(), SupportedExts) {
		return UnsupportedConfigError(v.getConfigType())
	}

	file, err := ioutil.ReadFile(v.getConfigFile())
	if err != nil {
		return err
	}

	return v.MergeConfig(bytes.NewReader(file))
}

// Viper will read a configuration file, setting existing keys to nil if the
// key does not exist in the file.
func ReadConfig(in io.Reader) error { return v.ReadConfig(in) }
func (v *Viper) ReadConfig(in io.Reader) error {
	v.config = make(map[string]interface{})
	return v.unmarshalReader(in, v.config)
}

// MergeConfig merges a new configuration with an existing config.
func MergeConfig(in io.Reader) error { return v.MergeConfig(in) }
func (v *Viper) MergeConfig(in io.Reader) error {
	if v.config == nil {
		v.config = make(map[string]interface{})
	}
	cfg := make(map[string]interface{})
	if err := v.unmarshalReader(in, cfg); err != nil {
		return err
	}
	mergeMaps(cfg, v.config, nil)
	return nil
}

func keyExists(k string, m map[string]interface{}) string {
	lk := strings.ToLower(k)
	for mk := range m {
		lmk := strings.ToLower(mk)
		if lmk == lk {
			return mk
		}
	}
	return ""
}

func castToMapStringInterface(
	src map[interface{}]interface{}) map[string]interface{} {
	tgt := map[string]interface{}{}
	for k, v := range src {
		tgt[fmt.Sprintf("%v", k)] = v
	}
	return tgt
}

// mergeMaps merges two maps. The `itgt` parameter is for handling go-yaml's
// insistence on parsing nested structures as `map[interface{}]interface{}`
// instead of using a `string` as the key for nest structures beyond one level
// deep. Both map types are supported as there is a go-yaml fork that uses
// `map[string]interface{}` instead.
func mergeMaps(
	src, tgt map[string]interface{}, itgt map[interface{}]interface{}) {
	for sk, sv := range src {
		tk := keyExists(sk, tgt)
		if tk == "" {
			out.Tracef("tk=\"\", tgt[%s]=%v", sk, sv)
			tgt[sk] = sv
			if itgt != nil {
				itgt[sk] = sv
			}
			continue
		}

		tv, ok := tgt[tk]
		if !ok {
			out.Tracef("tgt[%s] != ok, tgt[%s]=%v", tk, sk, sv)
			tgt[sk] = sv
			if itgt != nil {
				itgt[sk] = sv
			}
			continue
		}

		svType := reflect.TypeOf(sv)
		tvType := reflect.TypeOf(tv)
		if svType != tvType {
			out.Tracef(
				"svType != tvType; key=%s, st=%v, tt=%v, sv=%v, tv=%v",
				sk, svType, tvType, sv, tv)
			continue
		}

		out.Tracef("processing key=%s, st=%v, tt=%v, sv=%v, tv=%v",
			sk, svType, tvType, sv, tv)

		switch ttv := tv.(type) {
		case map[interface{}]interface{}:
			out.Tracef("merging maps (must convert)")
			tsv := sv.(map[interface{}]interface{})
			ssv := castToMapStringInterface(tsv)
			stv := castToMapStringInterface(ttv)
			mergeMaps(ssv, stv, ttv)
		case map[string]interface{}:
			out.Tracef("merging maps")
			mergeMaps(sv.(map[string]interface{}), ttv, nil)
		default:
			out.Tracef("setting value")
			tgt[tk] = sv
			if itgt != nil {
				itgt[tk] = sv
			}
		}
	}
}

// func ReadBufConfig(buf *bytes.Buffer) error { return v.ReadBufConfig(buf) }
// func (v *Viper) ReadBufConfig(buf *bytes.Buffer) error {
// 	v.config = make(map[string]interface{})
// 	return v.unmarshalReader(buf, v.config)
// }

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

func WatchRemoteConfig() error { return v.WatchRemoteConfig() }
func (v *Viper) WatchRemoteConfig() error {
	err := v.watchKeyValueConfig()
	if err != nil {
		return err
	}
	return nil
}

// unmarshalReader should unmarshall a Reader into a map
// Should probably be an unexported function
func unmarshalReader(in io.Reader, c map[string]interface{}) error {
	return v.unmarshalReader(in, c)
}

func (v *Viper) unmarshalReader(in io.Reader, c map[string]interface{}) error {
	return unmarshallConfigReader(in, c, v.getConfigType())
}

func (v *Viper) insensitiviseMaps() {
	insensitiviseMap(v.config)
	insensitiviseMap(v.defaults)
	insensitiviseMap(v.override)
	insensitiviseMap(v.kvstore)
}

// getKeyValueConfig retrieves the first found remote configuration
func (v *Viper) getKeyValueConfig() error {
	if RemoteConfig == nil {
		return RemoteConfigError("Enable the remote features by doing a blank import of the viper/remote package: '_ github.com/spf13/viper/remote'")
	}

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

func (v *Viper) getRemoteConfig(provider *defaultRemoteProvider) (map[string]interface{}, error) {

	reader, err := RemoteConfig.Get(provider)
	if err != nil {
		return nil, err
	}
	err = v.unmarshalReader(reader, v.kvstore)
	return v.kvstore, err
}

// retrieve the first found remote configuration
func (v *Viper) watchKeyValueConfig() error {
	for _, rp := range v.remoteProviders {
		val, err := v.watchRemoteConfig(rp)
		if err != nil {
			continue
		}
		v.kvstore = val
		return nil
	}
	return RemoteConfigError("No Files Found")
}

func (v *Viper) watchRemoteConfig(provider *defaultRemoteProvider) (map[string]interface{}, error) {
	reader, err := RemoteConfig.Watch(provider)
	if err != nil {
		return nil, err
	}
	err = v.unmarshalReader(reader, v.kvstore)
	return v.kvstore, err
}

// AllKeys returns all keys regardless where they are set
func AllKeys() []string { return v.AllKeys() }

// AllKeys is same as like named singleton (but drives off given *Viper)
func (v *Viper) AllKeys() []string {
	m := map[string]struct{}{}

	for key, _ := range v.defaults {
		m[strings.ToLower(key)] = struct{}{}
	}

	for key, _ := range v.pflags {
		m[strings.ToLower(key)] = struct{}{}
	}

	for key, _ := range v.env {
		m[strings.ToLower(key)] = struct{}{}
	}

	for key, _ := range v.config {
		m[strings.ToLower(key)] = struct{}{}
	}

	for key, _ := range v.kvstore {
		m[strings.ToLower(key)] = struct{}{}
	}

	for key, _ := range v.override {
		m[strings.ToLower(key)] = struct{}{}
	}

	for key, _ := range v.aliases {
		m[strings.ToLower(key)] = struct{}{}
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
		if b, _ := exists(filepath.Join(in, v.configName+"."+ext)); b {
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
	return "", ConfigFileNotFoundError{v.configName, fmt.Sprintf("%s", v.configPaths)}
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

// LookName is used for the String() method to dump a viper's user focused
// info (relating to what the DE can set in the env or in a config file) and
// will be a string set to either "json" or "text" (ie: String() will examine
// viper settings and get whatever "look" is set to and use that as the look)
var LookName = "look"

// VerboseName is used to decide to dump the information verbosely or not,
// so if "verbose" is set to 'true' (as a viper key) then verbose output is on
var VerboseName = "verbose"

// APIVersionName is needed for JSON output of the *Viper structure, if no
// api version is set then the JSON is bogus (defaults to "apiver" as the
// name of the key being looked for)
var APIVersionName = "apiver"

// TerseName is used to dump brief information about the viper cfg|env, so
// if "terse" is set as a key and is true then a reduced amount of data will
// be dumped (note that VerboseName's setting, if set, overrides this)
var TerseName = "terse"

// UserCfgTypeName is the viper config key that will be a string of either 'cfg'
// or 'env' to control the String() method returning data about what keys
// can be set in the config file or what env vars can be used by the user
var UserCfgTypeName = "globs"

// String will return a string with available config settings through either
// the env or via the config file so the user can see:
// - what settings are available, what is their current val (at least)
// - optionally show description and a user expertise level recommended
// This method leverages viper itself to decide what the look/format of
// the string is (text or json) and how to determine if verbose or
// terse mode is active via the exported package globs:
// - LookName defaults to "look" as the key to look for "text|json"
// - TerseName defaults to "terse" as the key, if true then terse
// - VerboseName defaults to "verbose" as the key, if true then verbose (overrides terse)
// - APIVersionName defaults to "apiver" and is required for JSON formatted output
func (v *Viper) String() string {
	verbosity := "regular"
	if v.GetBool(VerboseName) {
		verbosity = "verbose"
	} else if v.GetBool(TerseName) {
		verbosity = "terse"
	}
	// get the "look" (or format) of the outpu, "json" else defaults to text
	look := v.GetString(LookName)
	// config "globs" type desired ("env" for env vars, "cfg" for cfgfile)
	cfgGlobType := v.GetString(UserCfgTypeName)

	// Only "document" those settings that have descriptions, alphabetically:
	keys := []string{}
	for k := range v.desc {
		keys = append(keys, k)
	}
	sort.Strings(keys)

	type itemData struct {
		Description string      `json:"description,omitempty" pretty:"Description,omitempty"`
		UseLevel    string      `json:"useLevel,omitempty" pretty:"Use Level,omitempty"`
		Value       interface{} `json:"value"`
	}
	items := make([]interface{}, 0, 0)
	for _, k := range keys {
		var keyName string
		useKey := false
		useScope := v.useScope[k]
		if cfgGlobType == "cfg" && (useScope&AvailCfgFile) != 0 {
			keyName = k
			useKey = true
		} else if cfgGlobType == "env" && (useScope&AvailEnv) != 0 {
			keyName = v.mergeWithEnvPrefix(k)
			useKey = true
		}
		if !useKey {
			continue
		}
		var data itemData
		if verbosity != "terse" {
			data.Description = v.desc[k]
		}
		if verbosity == "verbose" {
			data.UseLevel = fmt.Sprintf("%s", v.useLevel[k])
		}
		data.Value = v.Get(k)
		currItem := make(map[string]interface{})
		currItem[keyName] = data
		items = append(items, currItem)
	}

	if look == "json" {
		fields := make([]string, 0, 0)
		fields = append(fields, "(name)")
		if verbosity != "terse" {
			fields = append(fields, "description")
		}
		if verbosity == "verbose" {
			fields = append(fields, "useLevel")
		}
		fields = append(fields, "value")
		// This will honor output indent levels and such as already specified,
		// see use of jsonindentlevel and such in cmds/dvln.go
		apiVer := v.GetString(APIVersionName)
		var output string
		var fatalProblem bool
		if apiVer != "" {
			output, fatalProblem = api.GetJSONOutput(apiVer, "dvlnGlobs", cfgGlobType, verbosity, fields, items)
		} else {
			output = fmt.Sprintf("No '%s' key is set internally so unable to dump JSON\n", APIVersionName)
			fatalProblem = true
		}
		if fatalProblem {
			// FIXME: erik: need to figure out something to do here... print
			// and die not good enough for server mode but "ok" for client mode,
			// note that an out.Fatal(output) won't print anything during test
			// runs (modify testViperJSONPrint() to not set apiver to see that)
			fmt.Fprintf(os.Stderr, "%s", output)
			out.Exit(-1)
		}
		return output
	}
	// The pretty String() method formats this for pretty text output, honoring
	// our output indent levels and such (see textindentlevel and texthumanize
	// settings in cmds/dvln.go and cmds/globals.go)
	return pretty.Sprintf("%# v", items)
}

// String implements a stringer for the UseLevel type so we can print out
// a string representations for the user use level setting
func (ul UseLevel) String() string {
	useLevel2String := map[UseLevel]string{
		NoviceUser:      "NOVICE",
		StandardUser:    "STANDARD",
		ExpertUser:      "EXPERT",
		AdminUser:       "ADMIN",
		InternalUse:     "INTERNAL",
		RestrictedUse:   "RESTRICTED",
		UnknownUseLevel: "UNKNOWN",
	}
	ul = useLevelCheck(ul)
	return useLevel2String[ul]
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
		return useLevel
	}
}
