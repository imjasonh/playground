-- Environment variables baked into the official Postgres image
SELECT key, value
FROM env
WHERE reference = 'postgres'
ORDER BY key;
