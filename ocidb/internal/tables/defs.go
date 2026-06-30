package tables

import (
	"fmt"
	"sort"
	"strings"

	fdw "github.com/values-conflict/go-sqlite-fdw"

	"github.com/imjasonh/playground/ocidb/internal/registry"
)

// filesContentCol is the index of the `content` column in the files table
// schema below. BestIndex sets it in the columns bitmask only when a query
// references content, letting the fetch skip reading file bodies otherwise.
const filesContentCol = 12

// defs is the catalog of virtual tables. Column order in each fetch function
// must match the order in the schema string exactly (including HIDDEN columns).
var defs = []tableDef{
	{
		name:   "tags",
		schema: `CREATE TABLE tags(tag TEXT, repository TEXT HIDDEN)`,
		params: []param{{name: "repository", col: 1, required: true}},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			repo := args["repository"]
			tagList, err := c.Tags(repo)
			if err != nil {
				return nil, err
			}
			rows := make([]fdw.Row, 0, len(tagList))
			for _, t := range tagList {
				rows = append(rows, fdw.Row{text(t), text(repo)})
			}
			return rows, nil
		},
	},
	{
		name: "manifest",
		schema: `CREATE TABLE manifest(
			reference TEXT HIDDEN,
			digest TEXT,
			media_type TEXT,
			size INTEGER,
			schema_version INTEGER,
			is_index INTEGER,
			num_manifests INTEGER,
			num_layers INTEGER,
			config_digest TEXT,
			raw TEXT
		)`,
		params: []param{{name: "reference", col: 0, required: true}},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			ref := args["reference"]
			mv, err := c.ManifestView(ref)
			if err != nil {
				return nil, err
			}
			numManifests := fdw.NullValue()
			numLayers := fdw.NullValue()
			configDigest := fdw.NullValue()
			if mv.IsIndex {
				numManifests = intVal(int64(len(mv.Children)))
			} else {
				numLayers = intVal(int64(len(mv.Layers)))
				configDigest = nullableText(mv.ConfigDigest)
			}
			return []fdw.Row{{
				text(ref),
				text(mv.Digest),
				text(mv.MediaType),
				intVal(mv.Size),
				intVal(mv.SchemaVersion),
				boolVal(mv.IsIndex),
				numManifests,
				numLayers,
				configDigest,
				text(string(mv.Raw)),
			}}, nil
		},
	},
	{
		name: "platforms",
		schema: `CREATE TABLE platforms(
			reference TEXT HIDDEN,
			os TEXT,
			architecture TEXT,
			variant TEXT,
			os_version TEXT,
			digest TEXT,
			media_type TEXT,
			size INTEGER
		)`,
		params: []param{{name: "reference", col: 0, required: true}},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			ref := args["reference"]
			descs, err := c.Platforms(ref)
			if err != nil {
				return nil, err
			}
			rows := make([]fdw.Row, 0, len(descs))
			for _, d := range descs {
				p := d.Platform
				os, arch, variant, osv := "", "", "", ""
				if p != nil {
					os, arch, variant, osv = p.OS, p.Architecture, p.Variant, p.OSVersion
				}
				rows = append(rows, fdw.Row{
					text(ref),
					nullableText(os),
					nullableText(arch),
					nullableText(variant),
					nullableText(osv),
					text(d.Digest.String()),
					text(string(d.MediaType)),
					intVal(d.Size),
				})
			}
			return rows, nil
		},
	},
	{
		name: "layers",
		schema: `CREATE TABLE layers(
			reference TEXT HIDDEN,
			platform TEXT HIDDEN,
			ordinal INTEGER,
			digest TEXT,
			media_type TEXT,
			size INTEGER
		)`,
		params: []param{
			{name: "reference", col: 0, required: true},
			{name: "platform", col: 1},
		},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			ref, plat := args["reference"], args["platform"]
			iv, err := c.ResolveImage(ref, plat)
			if err != nil {
				return nil, err
			}
			rows := make([]fdw.Row, 0, len(iv.Layers))
			for i, l := range iv.Layers {
				rows = append(rows, fdw.Row{
					text(ref),
					text(iv.Platform),
					intVal(int64(i + 1)),
					text(l.Digest.String()),
					text(string(l.MediaType)),
					intVal(l.Size),
				})
			}
			return rows, nil
		},
	},
	{
		name: "image",
		schema: `CREATE TABLE image(
			reference TEXT HIDDEN,
			platform TEXT HIDDEN,
			digest TEXT,
			config_digest TEXT,
			os TEXT,
			architecture TEXT,
			variant TEXT,
			created TEXT,
			author TEXT,
			docker_version TEXT,
			num_layers INTEGER,
			total_size INTEGER,
			user TEXT,
			working_dir TEXT,
			entrypoint TEXT,
			cmd TEXT,
			num_env INTEGER,
			num_labels INTEGER,
			num_exposed_ports INTEGER
		)`,
		params: []param{
			{name: "reference", col: 0, required: true},
			{name: "platform", col: 1},
		},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			ref, plat := args["reference"], args["platform"]
			iv, err := c.ResolveImage(ref, plat)
			if err != nil {
				return nil, err
			}
			cfg := iv.Config
			var totalSize int64
			for _, l := range iv.Layers {
				totalSize += l.Size
			}
			return []fdw.Row{{
				text(ref),
				text(iv.Platform),
				text(iv.ManifestDigest),
				text(iv.ConfigDigest),
				nullableText(cfg.OS),
				nullableText(cfg.Architecture),
				nullableText(cfg.Variant),
				timeVal(cfg.Created.Time),
				nullableText(cfg.Author),
				nullableText(cfg.DockerVersion),
				intVal(int64(len(iv.Layers))),
				intVal(totalSize),
				nullableText(cfg.Config.User),
				nullableText(cfg.Config.WorkingDir),
				jsonArray(cfg.Config.Entrypoint),
				jsonArray(cfg.Config.Cmd),
				intVal(int64(len(cfg.Config.Env))),
				intVal(int64(len(cfg.Config.Labels))),
				intVal(int64(len(cfg.Config.ExposedPorts))),
			}}, nil
		},
	},
	{
		name: "history",
		schema: `CREATE TABLE history(
			reference TEXT HIDDEN,
			platform TEXT HIDDEN,
			ordinal INTEGER,
			created TEXT,
			created_by TEXT,
			comment TEXT,
			empty_layer INTEGER
		)`,
		params: []param{
			{name: "reference", col: 0, required: true},
			{name: "platform", col: 1},
		},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			ref, plat := args["reference"], args["platform"]
			iv, err := c.ResolveImage(ref, plat)
			if err != nil {
				return nil, err
			}
			rows := make([]fdw.Row, 0, len(iv.Config.History))
			for i, h := range iv.Config.History {
				rows = append(rows, fdw.Row{
					text(ref),
					text(iv.Platform),
					intVal(int64(i + 1)),
					timeVal(h.Created.Time),
					nullableText(h.CreatedBy),
					nullableText(h.Comment),
					boolVal(h.EmptyLayer),
				})
			}
			return rows, nil
		},
	},
	{
		name: "env",
		schema: `CREATE TABLE env(
			reference TEXT HIDDEN,
			platform TEXT HIDDEN,
			key TEXT,
			value TEXT
		)`,
		params: []param{
			{name: "reference", col: 0, required: true},
			{name: "platform", col: 1},
		},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			ref, plat := args["reference"], args["platform"]
			iv, err := c.ResolveImage(ref, plat)
			if err != nil {
				return nil, err
			}
			rows := make([]fdw.Row, 0, len(iv.Config.Config.Env))
			for _, e := range iv.Config.Config.Env {
				k, v, _ := strings.Cut(e, "=")
				rows = append(rows, fdw.Row{text(ref), text(iv.Platform), text(k), text(v)})
			}
			return rows, nil
		},
	},
	{
		name: "labels",
		schema: `CREATE TABLE labels(
			reference TEXT HIDDEN,
			platform TEXT HIDDEN,
			key TEXT,
			value TEXT
		)`,
		params: []param{
			{name: "reference", col: 0, required: true},
			{name: "platform", col: 1},
		},
		fetch: func(c *registry.Client, args map[string]string, _ uint64) ([]fdw.Row, error) {
			ref, plat := args["reference"], args["platform"]
			iv, err := c.ResolveImage(ref, plat)
			if err != nil {
				return nil, err
			}
			keys := make([]string, 0, len(iv.Config.Config.Labels))
			for k := range iv.Config.Config.Labels {
				keys = append(keys, k)
			}
			sort.Strings(keys)
			rows := make([]fdw.Row, 0, len(keys))
			for _, k := range keys {
				rows = append(rows, fdw.Row{text(ref), text(iv.Platform), text(k), text(iv.Config.Config.Labels[k])})
			}
			return rows, nil
		},
	},
	{
		name: "files",
		schema: `CREATE TABLE files(
			reference TEXT HIDDEN,
			platform TEXT HIDDEN,
			layer INTEGER,
			layer_digest TEXT,
			path TEXT,
			type TEXT,
			size INTEGER,
			mode TEXT,
			linkname TEXT,
			uid INTEGER,
			gid INTEGER,
			modtime TEXT,
			content TEXT
		)`,
		// path is a regular (non-HIDDEN) column, but we still let an equality on
		// it push down so that `WHERE path = '/etc/os-release'` reads just that
		// one file instead of every body in the layer.
		params: []param{
			{name: "reference", col: 0, required: true},
			{name: "platform", col: 1},
			{name: "path", col: 4},
		},
		fetch: func(c *registry.Client, args map[string]string, cols uint64) ([]fdw.Row, error) {
			ref, plat, wantPath := args["reference"], args["platform"], args["path"]
			wantContent := cols&(1<<filesContentCol) != 0

			iv, err := c.ResolveImage(ref, plat)
			if err != nil {
				return nil, err
			}
			var rows []fdw.Row
			for i, l := range iv.Layers {
				digest := l.Digest.String()
				entries, err := c.LayerTOC(ref, digest)
				if err != nil {
					return nil, err
				}
				// Only crack open file bodies when the query asked for content.
				var bodies map[string][]byte
				if wantContent {
					var only map[string]bool
					if wantPath != "" {
						only = map[string]bool{wantPath: true}
					}
					bodies, err = c.ReadLayerFiles(ref, digest, only, registry.DefaultMaxFileSize)
					if err != nil {
						return nil, err
					}
				}
				for _, e := range entries {
					if wantPath != "" && e.Path != wantPath {
						continue
					}
					content := fdw.NullValue()
					if wantContent && e.Type == "file" {
						if body, ok := bodies[e.Path]; ok {
							content = textContent(body)
						}
					}
					rows = append(rows, fdw.Row{
						text(ref),
						text(iv.Platform),
						intVal(int64(i + 1)),
						text(digest),
						text(e.Path),
						text(e.Type),
						intVal(e.Size),
						text(fmt.Sprintf("%04o", e.Mode&0o7777)),
						nullableText(e.Linkname),
						intVal(int64(e.UID)),
						intVal(int64(e.GID)),
						timeVal(e.ModTime),
						content,
					})
				}
			}
			return rows, nil
		},
	},
}
