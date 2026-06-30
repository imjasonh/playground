-- Net lines contributed per author -- a JOIN across two virtual tables
SELECT c.author_name,
       sum(cf.additions)                 AS added,
       sum(cf.deletions)                 AS removed,
       sum(cf.additions - cf.deletions)  AS net
FROM commit_files cf
JOIN commits c ON c.hash = cf.commit_hash
WHERE cf.binary = 0
GROUP BY c.author_name
ORDER BY added DESC
LIMIT 15;
