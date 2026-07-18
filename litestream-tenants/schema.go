//go:build vfs

package main

import (
	"context"
	"database/sql"
	"fmt"
	"os"
)

const controlDBName = "control"

func repoDBName(repoID int64) string {
	return fmt.Sprintf("repo-%d", repoID)
}

const controlSchema = `
PRAGMA journal_mode=WAL;
PRAGMA synchronous=NORMAL;
CREATE TABLE tenants (
  id INTEGER PRIMARY KEY,
  slug TEXT NOT NULL UNIQUE,
  display_name TEXT NOT NULL,
  kind TEXT NOT NULL,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);
CREATE TABLE users (
  id INTEGER PRIMARY KEY,
  login TEXT NOT NULL UNIQUE,
  name TEXT,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);
CREATE TABLE orgs (
  id INTEGER PRIMARY KEY,
  tenant_id INTEGER NOT NULL REFERENCES tenants(id),
  login TEXT NOT NULL UNIQUE,
  name TEXT,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);
CREATE TABLE org_members (
  org_id INTEGER NOT NULL REFERENCES orgs(id),
  user_id INTEGER NOT NULL REFERENCES users(id),
  role TEXT NOT NULL,
  created_at TEXT NOT NULL,
  PRIMARY KEY (org_id, user_id)
);
CREATE TABLE repos (
  id INTEGER PRIMARY KEY,
  tenant_id INTEGER NOT NULL REFERENCES tenants(id),
  owner_type TEXT NOT NULL,
  owner_id INTEGER NOT NULL,
  name TEXT NOT NULL,
  full_name TEXT NOT NULL UNIQUE,
  replica_key TEXT NOT NULL UNIQUE,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);
CREATE INDEX repos_tenant ON repos(tenant_id);
CREATE TABLE repo_access (
  repo_id INTEGER NOT NULL REFERENCES repos(id),
  principal_type TEXT NOT NULL,
  principal_id INTEGER NOT NULL,
  permission TEXT NOT NULL,
  created_at TEXT NOT NULL,
  PRIMARY KEY (repo_id, principal_type, principal_id)
);
CREATE INDEX repo_access_principal ON repo_access(principal_type, principal_id);
`

const repoSchema = `
PRAGMA journal_mode=WAL;
PRAGMA synchronous=NORMAL;
CREATE TABLE pull_requests (
  id INTEGER PRIMARY KEY,
  number INTEGER NOT NULL UNIQUE,
  title TEXT NOT NULL,
  body TEXT,
  state TEXT NOT NULL,
  user_id INTEGER NOT NULL,
  user_login TEXT NOT NULL,
  base_ref TEXT NOT NULL,
  head_ref TEXT NOT NULL,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);
CREATE INDEX pr_updated ON pull_requests(updated_at);
CREATE TABLE issue_comments (
  id INTEGER PRIMARY KEY,
  pr_number INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  user_login TEXT NOT NULL,
  body TEXT NOT NULL,
  created_at TEXT NOT NULL,
  updated_at TEXT NOT NULL
);
CREATE INDEX comments_pr ON issue_comments(pr_number, created_at);
CREATE TABLE check_runs (
  id INTEGER PRIMARY KEY,
  pr_number INTEGER,
  name TEXT NOT NULL,
  status TEXT NOT NULL,
  conclusion TEXT,
  output_summary TEXT,
  completed_at TEXT
);
CREATE INDEX check_runs_pr ON check_runs(pr_number);
`

// WorldConfig sizes a synthetic control plane + per-repo DBs.
type WorldConfig struct {
	Tenants      int
	Users        int
	ReposPerTenant int
	PRsPerRepo   int
	CommentsPerPR int
	ChecksPerPR  int
	// BodyBytes is average PR/comment body size (typical schema lean/typical).
	BodyBytes int
}

func (c WorldConfig) withDefaults() WorldConfig {
	if c.Tenants < 1 {
		c.Tenants = 1
	}
	if c.Users < 1 {
		c.Users = 10
	}
	if c.ReposPerTenant < 1 {
		c.ReposPerTenant = 2
	}
	if c.PRsPerRepo < 1 {
		c.PRsPerRepo = 50
	}
	if c.CommentsPerPR < 0 {
		c.CommentsPerPR = 5
	}
	if c.ChecksPerPR < 0 {
		c.ChecksPerPR = 10
	}
	if c.BodyBytes < 0 {
		c.BodyBytes = 256
	}
	return c
}

func (c WorldConfig) RepoCount() int { return c.Tenants * c.ReposPerTenant }

// World is a seeded control DB + per-repo DBs ready for benches.
type World struct {
	H      *Harness
	Cfg    WorldConfig
	RepoIDs []int64
	UserIDs []int64
}

func SeedWorld(ctx context.Context, h *Harness, cfg WorldConfig) (*World, error) {
	cfg = cfg.withDefaults()
	w := &World{H: h, Cfg: cfg}

	controlPath := h.sourcePath(controlDBName)
	_ = os.Remove(controlPath)
	_ = os.Remove(controlPath + "-wal")
	_ = os.Remove(controlPath + "-shm")

	cdb, err := sql.Open("sqlite3", dsnLocal(controlPath))
	if err != nil {
		return nil, err
	}
	defer cdb.Close()
	if _, err := cdb.ExecContext(ctx, controlSchema); err != nil {
		return nil, fmt.Errorf("control schema: %w", err)
	}

	now := "2026-01-01T00:00:00Z"
	body := make([]byte, cfg.BodyBytes)
	for i := range body {
		body[i] = byte('a' + i%26)
	}
	bodyStr := string(body)

	for u := 1; u <= cfg.Users; u++ {
		id := int64(u)
		w.UserIDs = append(w.UserIDs, id)
		if _, err := cdb.ExecContext(ctx,
			`INSERT INTO users(id, login, name, created_at, updated_at) VALUES(?,?,?,?,?)`,
			id, fmt.Sprintf("user%d", u), fmt.Sprintf("User %d", u), now, now); err != nil {
			return nil, err
		}
	}

	repoID := int64(1000)
	for t := 1; t <= cfg.Tenants; t++ {
		tid := int64(t)
		if _, err := cdb.ExecContext(ctx,
			`INSERT INTO tenants(id, slug, display_name, kind, created_at, updated_at) VALUES(?,?,?,?,?,?)`,
			tid, fmt.Sprintf("tenant%d", t), fmt.Sprintf("Tenant %d", t), "org", now, now); err != nil {
			return nil, err
		}
		oid := int64(10000 + t)
		if _, err := cdb.ExecContext(ctx,
			`INSERT INTO orgs(id, tenant_id, login, name, created_at, updated_at) VALUES(?,?,?,?,?,?)`,
			oid, tid, fmt.Sprintf("org%d", t), fmt.Sprintf("Org %d", t), now, now); err != nil {
			return nil, err
		}
		// Every user is a member of every org in the small synthetic world (dense ACL).
		for _, uid := range w.UserIDs {
			role := "member"
			if uid == 1 {
				role = "admin"
			}
			if _, err := cdb.ExecContext(ctx,
				`INSERT INTO org_members(org_id, user_id, role, created_at) VALUES(?,?,?,?)`,
				oid, uid, role, now); err != nil {
				return nil, err
			}
		}

		for r := 0; r < cfg.ReposPerTenant; r++ {
			repoID++
			rid := repoID
			w.RepoIDs = append(w.RepoIDs, rid)
			name := fmt.Sprintf("repo%d", rid)
			full := fmt.Sprintf("org%d/%s", t, name)
			replicaKey := repoDBName(rid)
			if _, err := cdb.ExecContext(ctx, `
				INSERT INTO repos(id, tenant_id, owner_type, owner_id, name, full_name, replica_key, created_at, updated_at)
				VALUES(?,?,?,?,?,?,?,?,?)`,
				rid, tid, "org", oid, name, full, replicaKey, now, now); err != nil {
				return nil, err
			}
			// Explicit user access for user 1..min(5,Users) — models collaborators.
			limit := 5
			if limit > cfg.Users {
				limit = cfg.Users
			}
			for u := 1; u <= limit; u++ {
				if _, err := cdb.ExecContext(ctx, `
					INSERT INTO repo_access(repo_id, principal_type, principal_id, permission, created_at)
					VALUES(?,?,?,?,?)`, rid, "user", int64(u), "write", now); err != nil {
					return nil, err
				}
			}

			if err := seedRepoDB(ctx, h, rid, cfg, bodyStr, now); err != nil {
				return nil, err
			}
		}
	}

	if err := cdb.Close(); err != nil {
		return nil, err
	}
	if err := h.replicateOnce(ctx, controlDBName, controlPath); err != nil {
		return nil, fmt.Errorf("replicate control: %w", err)
	}

	fi, _ := os.Stat(controlPath)
	fmt.Printf("seeded control db size=%s tenants=%d users=%d repos=%d\n",
		humanBytes(fi.Size()), cfg.Tenants, cfg.Users, len(w.RepoIDs))
	return w, nil
}

func seedRepoDB(ctx context.Context, h *Harness, repoID int64, cfg WorldConfig, body, now string) error {
	name := repoDBName(repoID)
	path := h.sourcePath(name)
	_ = os.Remove(path)
	_ = os.Remove(path + "-wal")
	_ = os.Remove(path + "-shm")

	db, err := sql.Open("sqlite3", dsnLocal(path))
	if err != nil {
		return err
	}
	if _, err := db.ExecContext(ctx, repoSchema); err != nil {
		_ = db.Close()
		return fmt.Errorf("repo schema %s: %w", name, err)
	}

	tx, err := db.BeginTx(ctx, nil)
	if err != nil {
		_ = db.Close()
		return err
	}
	prStmt, err := tx.PrepareContext(ctx, `
		INSERT INTO pull_requests(id, number, title, body, state, user_id, user_login, base_ref, head_ref, created_at, updated_at)
		VALUES(?,?,?,?,?,?,?,?,?,?,?)`)
	if err != nil {
		_ = tx.Rollback()
		_ = db.Close()
		return err
	}
	cmtStmt, err := tx.PrepareContext(ctx, `
		INSERT INTO issue_comments(id, pr_number, user_id, user_login, body, created_at, updated_at)
		VALUES(?,?,?,?,?,?,?)`)
	if err != nil {
		_ = prStmt.Close()
		_ = tx.Rollback()
		_ = db.Close()
		return err
	}
	chkStmt, err := tx.PrepareContext(ctx, `
		INSERT INTO check_runs(id, pr_number, name, status, conclusion, output_summary, completed_at)
		VALUES(?,?,?,?,?,?,?)`)
	if err != nil {
		_ = cmtStmt.Close()
		_ = prStmt.Close()
		_ = tx.Rollback()
		_ = db.Close()
		return err
	}

	var cmtID, chkID int64
	for n := 1; n <= cfg.PRsPerRepo; n++ {
		prID := repoID*1_000_000 + int64(n)
		uid := int64((n % cfg.Users) + 1)
		if _, err := prStmt.ExecContext(ctx, prID, n,
			fmt.Sprintf("PR %d", n), body, "open",
			uid, fmt.Sprintf("user%d", uid), "main", fmt.Sprintf("feat/%d", n),
			now, now); err != nil {
			_ = chkStmt.Close()
			_ = cmtStmt.Close()
			_ = prStmt.Close()
			_ = tx.Rollback()
			_ = db.Close()
			return err
		}
		for c := 0; c < cfg.CommentsPerPR; c++ {
			cmtID++
			cuid := int64((c % cfg.Users) + 1)
			if _, err := cmtStmt.ExecContext(ctx, cmtID, n, cuid, fmt.Sprintf("user%d", cuid), body, now, now); err != nil {
				_ = chkStmt.Close()
				_ = cmtStmt.Close()
				_ = prStmt.Close()
				_ = tx.Rollback()
				_ = db.Close()
				return err
			}
		}
		for k := 0; k < cfg.ChecksPerPR; k++ {
			chkID++
			if _, err := chkStmt.ExecContext(ctx, chkID, n,
				fmt.Sprintf("check-%d", k), "completed", "success", "ok", now); err != nil {
				_ = chkStmt.Close()
				_ = cmtStmt.Close()
				_ = prStmt.Close()
				_ = tx.Rollback()
				_ = db.Close()
				return err
			}
		}
	}
	_ = chkStmt.Close()
	_ = cmtStmt.Close()
	_ = prStmt.Close()
	if err := tx.Commit(); err != nil {
		_ = db.Close()
		return err
	}
	if err := db.Close(); err != nil {
		return err
	}
	if err := h.replicateOnce(ctx, name, path); err != nil {
		return fmt.Errorf("replicate %s: %w", name, err)
	}
	fi, err := os.Stat(path)
	if err != nil {
		return err
	}
	fmt.Printf("seeded %s size=%s prs=%d\n", name, humanBytes(fi.Size()), cfg.PRsPerRepo)
	return nil
}

// AuthorizeRepo models the control-plane lookup on every repo API call:
// user must have explicit repo_access OR be an org member of the owning org.
func AuthorizeRepo(ctx context.Context, control *sql.DB, userID, repoID int64) (permission string, ok bool, err error) {
	err = control.QueryRowContext(ctx, `
		SELECT permission FROM repo_access
		WHERE repo_id = ? AND principal_type = 'user' AND principal_id = ?
		LIMIT 1`, repoID, userID).Scan(&permission)
	if err == nil {
		return permission, true, nil
	}
	if err != sql.ErrNoRows {
		return "", false, err
	}
	err = control.QueryRowContext(ctx, `
		SELECT om.role
		FROM repos r
		JOIN orgs o ON o.id = r.owner_id AND r.owner_type = 'org'
		JOIN org_members om ON om.org_id = o.id
		WHERE r.id = ? AND om.user_id = ?
		LIMIT 1`, repoID, userID).Scan(&permission)
	if err == sql.ErrNoRows {
		return "", false, nil
	}
	if err != nil {
		return "", false, err
	}
	return permission, true, nil
}

func readPR(ctx context.Context, repo *sql.DB, number int) (title string, err error) {
	err = repo.QueryRowContext(ctx, `SELECT title FROM pull_requests WHERE number = ?`, number).Scan(&title)
	return title, err
}

func writeComment(ctx context.Context, repo *sql.DB, prNumber int, userID int64) error {
	_, err := repo.ExecContext(ctx, `
		INSERT INTO issue_comments(pr_number, user_id, user_login, body, created_at, updated_at)
		VALUES(?,?,?,?,datetime('now'),datetime('now'))`,
		prNumber, userID, fmt.Sprintf("user%d", userID), "bench comment")
	return err
}

func controlGrantAccess(ctx context.Context, control *sql.DB, repoID, userID int64) error {
	_, err := control.ExecContext(ctx, `
		INSERT OR REPLACE INTO repo_access(repo_id, principal_type, principal_id, permission, created_at)
		VALUES(?,?,?,?,datetime('now'))`, repoID, "user", userID, "write")
	return err
}
