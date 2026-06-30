-- Full-text-ish search: files whose contents mention "recursively".
-- contents is read lazily per file; binary files are skipped (NULL).
-- Add `AND ref = '<branch|tag|sha>'` to search a different revision.
SELECT path,
       lines
FROM files
WHERE contents LIKE '%recursively%'
ORDER BY path;
