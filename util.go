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

	"github.com/BurntSushi/toml"
	"github.com/dvln/out"
	"github.com/magiconair/properties"
	"github.com/spf13/cast"
	"gopkg.in/yaml.v2"
)

// insensitiviseMap turns the keys into lower case (case insensitive)
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

// AbsPathify takes a path and attempts to clean it up and turn
// it into an absolute path via filepath.Clean and filepath.Abs
func AbsPathify(inPath string) string {
	//out.Traceln("Trying to resolve absolute path to", inPath)

	if strings.HasPrefix(inPath, "$HOME") {
		inPath = UserHomeDir() + inPath[5:]
	}

	if strings.HasPrefix(inPath, "$") {
		end := strings.Index(inPath, string(os.PathSeparator))
		inPath = os.Getenv(inPath[1:end]) + inPath[end:]
	}

	if strings.HasPrefix(inPath, "~") {
		inPath = UserHomeDir() + inPath[1:]
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

// Exists checks if given file/dir exists
func Exists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return false, err
}

// StringInSlice is checking exactly that, is the string in the slice
func StringInSlice(a string, list []string) bool {
	for _, b := range list {
		if b == a {
			return true
		}
	}
	return false
}

// UserHomeDir figures out the users home dir
func UserHomeDir() string {
	if runtime.GOOS == "windows" {
		home := os.Getenv("HOMEDRIVE") + os.Getenv("HOMEPATH")
		if home == "" {
			home = os.Getenv("USERPROFILE")
		}
		return home
	}
	return os.Getenv("HOME")
}

// FindCWD tries to find the current working directory
func FindCWD() (string, error) {
	serverFile, err := filepath.Abs(os.Args[0])

	if err != nil {
		return "", fmt.Errorf("Can't get absolute path for executable: %v", err)
	}

	path := filepath.Dir(serverFile)
	realFile, err := filepath.EvalSymlinks(serverFile)

	if err != nil {
		if _, err = os.Stat(serverFile + ".exe"); err == nil {
			realFile = filepath.Clean(serverFile + ".exe")
		}
	}

	if err == nil && realFile != serverFile {
		path = filepath.Dir(realFile)
	}

	return path, nil
}

// marshallConfigReader reads from the given io.Reader and unmarshals
// the results into the given map 'c' (adding to it potentially) for
// the given config type (yaml/yml, json, toml) with case insensitive
// keys (lower case basically)
func marshallConfigReader(in io.Reader, c map[string]interface{}, configType string) {
	buf := new(bytes.Buffer)
	buf.ReadFrom(in)

	switch configType {
	case "yaml", "yml":
		if err := yaml.Unmarshal(buf.Bytes(), &c); err != nil {
			out.Fatalf("Error parsing config: %s", err)
		}

	case "json":
		if err := json.Unmarshal(buf.Bytes(), &c); err != nil {
			out.Fatalf("Error parsing config: %s", err)
		}

	case "toml":
		if _, err := toml.Decode(buf.String(), &c); err != nil {
			out.Fatalf("Error parsing config: %s", err)
		}

	case "properties", "props", "prop":
		var p *properties.Properties
		var err error
		if p, err = properties.Load(buf.Bytes(), properties.UTF8); err != nil {
			out.Fatalf("Error parsing config: %s", err)
		}
		for _, key := range p.Keys() {
			value, _ := p.Get(key)
			c[key] = value
		}
	}

	// make all keys lower case (case insensitive)
	insensitiviseMap(c)
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
