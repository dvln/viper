// Modified copy of spf13's viper util.go to trim out some debug statements
// that seemed a bit too verbose (and switch them to 'out' pkg trace statements
// in case they are wanted back one can uncomment them)
//
// Copyright from spf13:
// Copyright © 2014 Steve Francia <spf@spf13.com>.
//
// Use of this source code is governed by an MIT-style
// license that can be found in the LICENSE file.

// Viper is a application configuration system.
// It believes that applications can be configured a variety of ways
// via flags, ENVIRONMENT variables, configuration files retrieved
// from the file system, or a remote key/value store.

package viper

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"reflect"
	"runtime"
	"strings"
	"unicode"

	"github.com/dvln/cast"
	"github.com/dvln/hcl"
	"github.com/dvln/out"
	"github.com/dvln/properties"
	"github.com/dvln/toml"
	"github.com/dvln/yaml"
)

// Denotes failing to parse configuration file.
type ConfigParseError struct {
	err error
}

// Returns the formatted configuration error.
func (pe ConfigParseError) Error() string {
	return fmt.Sprintf("While parsing config: %s", pe.err.Error())
}

func insensitiviseMap(m map[string]interface{}) {
	for key, val := range m {
		lower := strings.ToLower(key)
		if key != lower {
			delete(m, key)
			m[lower] = val
		}

		if val != nil && reflect.TypeOf(val).Kind() == reflect.Map {
			insensitiviseMap(cast.ToStringMap(val))
		}
	}
}

// absPathify takes a path and attempts to clean it up and turn
// it into an absolute path via filepath.Clean and filepath.Abs
func absPathify(inPath string) string {
	if strings.HasPrefix(inPath, "$HOME") {
		inPath = userHomeDir() + inPath[5:]
	}

	if strings.HasPrefix(inPath, "$") {
		end := strings.Index(inPath, string(os.PathSeparator))
		inPath = os.Getenv(inPath[1:end]) + inPath[end:]
	}

	if strings.HasPrefix(inPath, "~") {
		inPath = userHomeDir() + inPath[1:]
	}

	if filepath.IsAbs(inPath) {
		return filepath.Clean(inPath)
	}

	p, err := filepath.Abs(inPath)
	if err == nil {
		return filepath.Clean(p)
	}
	out.Errorln("Couldn't discover absolute path for:", inPath)
	out.Errorln("  Error:", err)
	return ""
}

// exists checks if given file/dir exists
func exists(path string) (bool, error) {
	_, err := filesys.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return false, err
}

// stringInSlice is checking exactly that, is the string in the slice
func stringInSlice(a string, list []string) bool {
	for _, b := range list {
		if b == a {
			return true
		}
	}
	return false
}

// userHomeDir figures out the users home dir
func userHomeDir() string {
	if runtime.GOOS == "windows" {
		home := os.Getenv("HOMEDRIVE") + os.Getenv("HOMEPATH")
		if home == "" {
			home = os.Getenv("USERPROFILE")
		}
		return home
	}
	return os.Getenv("HOME")
}

// findCWD tries to find the current working directory
func findCWD() (string, error) {
	serverFile, err := filepath.Abs(os.Args[0])

	if err != nil {
		return "", fmt.Errorf("Can't get absolute path for executable: %v", err)
	}

	path := filepath.Dir(serverFile)
	realFile, err := filepath.EvalSymlinks(serverFile)

	if err != nil {
		if _, err = filesys.Stat(serverFile + ".exe"); err == nil {
			realFile = filepath.Clean(serverFile + ".exe")
		}
	}

	if err == nil && realFile != serverFile {
		path = filepath.Dir(realFile)
	}

	return path, nil
}

func unmarshallConfigReader(in io.Reader, c map[string]interface{}, configType string) error {
	buf := new(bytes.Buffer)
	buf.ReadFrom(in)

	switch strings.ToLower(configType) {
	case "yaml", "yml":
		if err := yaml.Unmarshal(buf.Bytes(), &c); err != nil {
			return ConfigParseError{err}
		}

	case "json":
		if err := json.Unmarshal(buf.Bytes(), &c); err != nil {
			return ConfigParseError{err}
		}

	case "hcl":
		obj, err := hcl.Parse(string(buf.Bytes()))
		if err != nil {
			return ConfigParseError{err}
		}
		if err = hcl.DecodeObject(&c, obj); err != nil {
			return ConfigParseError{err}
		}

	case "toml":
		if _, err := toml.Decode(buf.String(), &c); err != nil {
			return ConfigParseError{err}
		}

	case "properties", "props", "prop":
		var p *properties.Properties
		var err error
		if p, err = properties.Load(buf.Bytes(), properties.UTF8); err != nil {
			return ConfigParseError{err}
		}
		for _, key := range p.Keys() {
			value, _ := p.Get(key)
			c[key] = value
		}
	}

	// make all keys lower case (case insensitive)
	insensitiviseMap(c)
	return nil
}

func safeMul(a, b uint) uint {
	c := a * b
	if a > 1 && b > 1 && c/b != a {
		return 0
	}
	return c
}

// parseSizeInBytes converts strings like 1GB or 12 mb into an unsigned integer number of bytes
func parseSizeInBytes(sizeStr string) uint {
	sizeStr = strings.TrimSpace(sizeStr)
	lastChar := len(sizeStr) - 1
	multiplier := uint(1)

	if lastChar > 0 {
		if sizeStr[lastChar] == 'b' || sizeStr[lastChar] == 'B' {
			if lastChar > 1 {
				switch unicode.ToLower(rune(sizeStr[lastChar-1])) {
				case 'k':
					multiplier = 1 << 10
					sizeStr = strings.TrimSpace(sizeStr[:lastChar-1])
				case 'm':
					multiplier = 1 << 20
					sizeStr = strings.TrimSpace(sizeStr[:lastChar-1])
				case 'g':
					multiplier = 1 << 30
					sizeStr = strings.TrimSpace(sizeStr[:lastChar-1])
				default:
					multiplier = 1
					sizeStr = strings.TrimSpace(sizeStr[:lastChar])
				}
			}
		}
	}

	size := cast.ToInt(sizeStr)
	if size < 0 {
		size = 0
	}

	return safeMul(uint(size), multiplier)
}
