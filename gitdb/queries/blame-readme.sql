-- Who owns the most lines of README.md right now?
-- (Change the path to blame any tracked file.)
SELECT author_name,
       count(*)  AS lines
FROM blame
WHERE path = 'README.md'
GROUP BY author_name
ORDER BY lines DESC
LIMIT 15;
