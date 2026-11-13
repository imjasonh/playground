package telemetry

import "go.opentelemetry.io/otel/attribute"

// Metric attribute keys shared by every component, so one dashboard query
// can group cas, cascache, and runner series the same way.
const (
	// AttrInstance is the REAPI instance name, which is the tenant's
	// namespace.
	AttrInstance = attribute.Key("instance")
	// AttrPeer is the kind of client that made a call; see Peer.
	AttrPeer = attribute.Key("peer")
	// AttrDirection is "read" or "write", from the server's side.
	AttrDirection = attribute.Key("direction")
	// AttrAPI is the call that moved the bytes: batch or bytestream.
	AttrAPI = attribute.Key("api")
	// AttrResult is a lookup's result, such as hit or miss.
	AttrResult = attribute.Key("result")
	// AttrOutcome is how a unit of work ended, such as ok or error.
	AttrOutcome = attribute.Key("outcome")
	// AttrStage is a step of executing an action on a runner.
	AttrStage = attribute.Key("stage")
	// AttrInputMode is how a runner built the exec root: copy, fuse, or
	// volume.
	AttrInputMode = attribute.Key("input_mode")
	// AttrMnemonic is the Bazel action mnemonic, such as GoCompile.
	AttrMnemonic = attribute.Key("mnemonic")

	attrDir = attribute.Key("dir")
)
