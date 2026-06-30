-- Lines of (text) code by top-level directory at HEAD
SELECT CASE WHEN instr(path, '/') > 0
            THEN substr(path, 1, instr(path, '/') - 1)
            ELSE '(root)' END   AS dir,
       count(*)                 AS files,
       sum(lines)               AS lines
FROM files
WHERE is_binary = 0
GROUP BY dir
ORDER BY lines DESC
LIMIT 20;
