// Command eventlog keeps a copy of every Event in a volume, so the copies
// outlast the hour that the API server keeps Events, like
// resmoio/kubernetes-event-exporter writing to a file. It serves the copies
// of a namespace's Events, oldest first:
//
//	GET /events/NAMESPACE
//
// It shows a program that keeps state on disk with kube.Volume. The
// generate command gives it a PersistentVolumeClaim, mounted at
// /var/lib/eventlog, and runs one replica, which writes the volume. So that
// a copy survives a crash of the program or its node, the program writes a
// new file, syncs it, renames it over the old copy, and syncs the
// directory. It skips a copy that it can't read instead of failing the
// whole namespace. A caller sends a service account token for the audience
// "eventlog", and can read the Events of its own namespace.
package main

import (
	"bytes"
	"cmp"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"io/fs"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"time"

	"github.com/imjasonh/playground/kube"
)

// volume is where generate mounts the program's volume.
const volume = "/var/lib/eventlog"

// Event is a Kubernetes Event, with the fields that the program keeps.
type Event struct {
	kube.Object    `kube:"apiVersion=v1,kind=Event,scope=Namespaced"`
	InvolvedObject ObjectReference `json:"involvedObject"`
	Reason         string          `json:"reason,omitempty"`
	Message        string          `json:"message,omitempty"`
	Type           string          `json:"type,omitempty"`
	Count          int32           `json:"count,omitempty"`
	LastTimestamp  time.Time       `json:"lastTimestamp,omitzero"`
}

// ObjectReference names the object that an Event is about.
type ObjectReference struct {
	Kind string `json:"kind,omitempty"`
	Name string `json:"name,omitempty"`
}

// Record is the copy of an Event that the program keeps and serves.
type Record struct {
	Name    string          `json:"name"`
	Object  ObjectReference `json:"object"`
	Reason  string          `json:"reason,omitempty"`
	Message string          `json:"message,omitempty"`
	Type    string          `json:"type,omitempty"`
	Count   int32           `json:"count,omitempty"`
	Last    time.Time       `json:"last,omitzero"`
}

type eventLog struct {
	// dir is a pointer so a flag can set it after the controller is built.
	dir *string
}

// Reconcile writes the Event's copy to DIR/NAMESPACE/UID.json. The copy stays
// after the Event is deleted.
func (l *eventLog) Reconcile(ctx context.Context, e *Event) error {
	b, err := json.Marshal(Record{
		Name: e.Name, Object: e.InvolvedObject, Reason: e.Reason, Message: e.Message,
		Type: e.Type, Count: e.Count, Last: e.LastTimestamp,
	})
	if err != nil {
		return err
	}
	dir := filepath.Join(*l.dir, e.Namespace)
	path := filepath.Join(dir, e.UID+".json")
	if old, err := os.ReadFile(path); err == nil && bytes.Equal(old, b) {
		return nil
	}
	if _, err := os.Stat(dir); errors.Is(err, fs.ErrNotExist) {
		if err := os.MkdirAll(dir, 0o700); err != nil {
			return err
		}
		if err := syncDir(*l.dir); err != nil {
			return err
		}
	}
	// A copy written in place would be cut short if the program stopped
	// partway, so write a new file and rename it over the old one. Sync the
	// file before the rename, and the directory after it, or a crash of the
	// node can leave the new name with an empty file, or the old copy.
	f, err := os.CreateTemp(dir, ".event-")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	if _, err := f.Write(b); err != nil {
		f.Close()
		return err
	}
	if err := f.Sync(); err != nil {
		f.Close()
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	if err := os.Rename(f.Name(), path); err != nil {
		return err
	}
	return syncDir(dir)
}

// syncDir writes dir's entries to disk, so that the files created and
// renamed in it survive a crash.
func syncDir(dir string) error {
	d, err := os.Open(dir)
	if err != nil {
		return err
	}
	defer d.Close()
	return d.Sync()
}

// api serves the copies.
type api struct {
	dir, audience *string
}

func (a *api) handler() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("GET /events/{namespace}", a.events)
	return mux
}

func (a *api) events(w http.ResponseWriter, r *http.Request) {
	token, _ := strings.CutPrefix(r.Header.Get("Authorization"), "Bearer ")
	review, err := kube.ReviewToken(r.Context(), token, *a.audience)
	switch {
	case err != nil:
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	case !review.Authenticated:
		w.Header().Set("WWW-Authenticate", "Bearer")
		http.Error(w, review.Error, http.StatusUnauthorized)
		return
	}
	ns := r.PathValue("namespace")
	if own, _, _ := review.User.ServiceAccount(); own != ns {
		http.Error(w, review.User.Username+" can't read the Events of "+ns, http.StatusForbidden)
		return
	}
	paths, err := filepath.Glob(filepath.Join(*a.dir, ns, "*.json"))
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	records := []Record{}
	for _, p := range paths {
		// Skip a copy that can't be read, such as one that a disk error
		// damaged, so that one bad copy doesn't hide the rest. While the
		// Event exists, its next reconcile, at the latest when the program
		// starts, writes the copy again.
		var rec Record
		b, err := os.ReadFile(p)
		if err == nil {
			err = json.Unmarshal(b, &rec)
		}
		if err != nil {
			slog.WarnContext(r.Context(), "skipping a copy of an Event that can't be read", "path", p, "err", err)
			continue
		}
		records = append(records, rec)
	}
	slices.SortFunc(records, func(a, b Record) int {
		return cmp.Or(a.Last.Compare(b.Last), cmp.Compare(a.Name, b.Name))
	})
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(records)
}

func main() {
	dir := flag.String("dir", volume, "directory to keep the copies of Events in")
	audience := flag.String("audience", "eventlog", "audience that callers' tokens must have")
	kube.Main(
		kube.For[Event](&eventLog{dir: dir}),
		kube.Serve((&api{dir: dir, audience: audience}).handler()),
		kube.Volume(volume),
	)
}
