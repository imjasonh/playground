-- Which OS / CPU architectures is the official Go image built for?
SELECT os, architecture, variant
FROM platforms
WHERE reference = 'golang'
ORDER BY os, architecture, variant;
