-- The five largest layers in python:3.12-slim (linux/amd64)
SELECT ordinal,
       substr(digest, 1, 19) AS digest,
       printf('%.1f MB', size / 1048576.0) AS size_mb
FROM layers
WHERE reference = 'python:3.12-slim'
ORDER BY size DESC
LIMIT 5;
