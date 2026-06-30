-- Repository summary: commits, branches, tags, files, and the active span
SELECT
  (SELECT count(*) FROM commits)                                  AS commits,
  (SELECT count(*) FROM refs WHERE is_branch)                     AS branches,
  (SELECT count(*) FROM tags)                                     AS tags,
  (SELECT count(*) FROM files)                                    AS files_at_head,
  (SELECT min(date(author_unix, 'unixepoch')) FROM commits)       AS first_commit,
  (SELECT max(date(author_unix, 'unixepoch')) FROM commits)       AS latest_commit;
