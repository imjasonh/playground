-- Bytes that ride along in the image's layers but never reach the final
-- (squashed) filesystem: files that a higher layer replaced or deleted, so
-- present = 0. They inflate the download without contributing to the running
-- image -- here, redis rewrites its dpkg/debconf state and /etc/ld.so.cache
-- across build steps. (type = 'file' and whiteout IS NULL keep this to real
-- content, not the tiny whiteout markers that do the deleting.)
SELECT layer,
       path,
       printf('%.1f KB', size / 1024.0) AS wasted
FROM files
WHERE reference = 'redis' AND present = 0 AND type = 'file' AND whiteout IS NULL
ORDER BY size DESC
LIMIT 12;
