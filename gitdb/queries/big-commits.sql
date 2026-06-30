-- Largest non-merge commits by lines changed (text files only)
SELECT substr(c.hash, 1, 10)             AS rev,
       date(c.author_unix, 'unixepoch')  AS day,
       c.author_name,
       sum(cf.additions + cf.deletions)  AS churn,
       count(*)                          AS files
FROM commits c
JOIN commit_files cf ON cf.commit_hash = c.hash
WHERE c.is_merge = 0 AND cf.binary = 0
GROUP BY c.hash
ORDER BY churn DESC
LIMIT 15;
