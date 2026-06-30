-- Redis download size across CPU architectures. Both the reference (constant)
-- and the platform (from the CTE join) are pushed into the layers table.
WITH plats(platform) AS (VALUES ('linux/amd64'), ('linux/arm64'), ('linux/arm/v7'))
SELECT plats.platform,
       count(*) AS layers,
       printf('%.2f MB', sum(l.size) / 1048576.0) AS download_size
FROM plats
JOIN layers l ON l.reference = 'redis' AND l.platform = plats.platform
GROUP BY plats.platform
ORDER BY plats.platform;
