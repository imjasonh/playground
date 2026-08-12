package a

const (
	awsKey = "AKIAIOSFODNN7EXAMPLE"                     // want `looks like an AWS access key`
	ghTok  = "ghp_abcdefghijklmnopqrstuvwxyz0123456789" // want `looks like a GitHub token`
	slack  = "xoxb-PASTA-FIXTURE-NOT-A-SECRET"          // want `looks like a Slack token`
	pem    = "-----BEGIN RSA PRIVATE KEY-----\nABC..."  // want `PEM private-key header`
	safe   = "this is just a regular string"
	url    = "https://example.com/api"
)
