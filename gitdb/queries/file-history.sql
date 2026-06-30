-- Every change that touched README.md, newest first
-- (join commit_files to commits; change the path to follow any file)
SELECT c.author_when,
       substr(cf.commit_hash, 1, 10)  AS rev,
       cf.change,
       cf.additions,
       cf.deletions,
       c.author_name
FROM commit_files cf
JOIN commits c ON c.hash = cf.commit_hash
WHERE cf.path = 'README.md'
ORDER BY c.author_unix DESC
LIMIT 20;
