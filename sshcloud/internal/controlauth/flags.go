package controlauth

import (
	"flag"
	"time"
)

// TLSFlags owns the common reloadable control-certificate command flags.
type TLSFlags struct {
	BundleDir      string
	BundleMaxAge   time.Duration
	CertFile       string
	KeyFile        string
	CurrentCAFile  string
	PreviousCAFile string
}

// RegisterTLSFlags adds the shared control TLS flags to fs.
func RegisterTLSFlags(fs *flag.FlagSet, role Role) *TLSFlags {
	var flags TLSFlags
	name := string(role)
	fs.StringVar(&flags.CertFile, "control-cert", "", "reloadable "+name+" control certificate PEM")
	fs.StringVar(&flags.KeyFile, "control-key", "", "reloadable "+name+" control private-key PEM")
	fs.StringVar(&flags.CurrentCAFile, "control-ca-current", "", "reloadable current control CA PEM")
	fs.StringVar(&flags.PreviousCAFile, "control-ca-previous", "", "reloadable previous control CA PEM")
	fs.StringVar(&flags.BundleDir, "control-bundle", "", "atomically switched control TLS bundle directory")
	fs.DurationVar(&flags.BundleMaxAge, "control-bundle-max-age", DefaultBundleLease, "last-known-good control bundle lease")
	return &flags
}

// Files returns the parsed TLS bundle configuration.
func (f *TLSFlags) Files() TLSFiles {
	return TLSFiles{
		BundleDir: f.BundleDir, MaxAge: f.BundleMaxAge,
		CertFile: f.CertFile, KeyFile: f.KeyFile,
		CurrentCAFile: f.CurrentCAFile, PreviousCAFile: f.PreviousCAFile,
	}
}

// Fresh checks the configured bundle's last-known-good lease.
func (f *TLSFlags) Fresh() error {
	return BundleFresh(f.BundleDir, f.BundleMaxAge)
}
