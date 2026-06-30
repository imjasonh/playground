-- Alpine 3.x version tags, sorted (SQLite filters the tag list we fetched)
SELECT tag
FROM tags
WHERE repository = 'library/alpine'
  AND tag LIKE '3.%'
ORDER BY tag;
