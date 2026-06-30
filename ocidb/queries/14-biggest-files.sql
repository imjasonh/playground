-- The 10 largest files in the debian image by uncompressed size, read straight
-- from the layer tables of contents (no file bodies needed). Swap in any other
-- image to see what is taking up the most space inside it.
SELECT path,
       printf('%.2f MB', size / 1048576.0) AS size
FROM files
WHERE reference = 'debian' AND type = 'file'
ORDER BY size DESC
LIMIT 10;
