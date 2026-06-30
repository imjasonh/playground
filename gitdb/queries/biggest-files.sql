-- Largest text files currently tracked at HEAD
SELECT path,
       size,
       lines
FROM files
WHERE is_binary = 0
ORDER BY size DESC
LIMIT 15;
