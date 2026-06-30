-- Hotspots: files with the most churn (lines added + removed) across all history
SELECT path,
       count(*)                    AS touched_by_commits,
       sum(additions)              AS added,
       sum(deletions)              AS removed,
       sum(additions + deletions)  AS churn
FROM commit_files
WHERE binary = 0
GROUP BY path
ORDER BY churn DESC
LIMIT 15;
