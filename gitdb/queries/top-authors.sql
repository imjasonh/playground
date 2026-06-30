-- Most prolific authors by commit count
SELECT author_name,
       count(*)                                  AS commits,
       min(date(author_unix, 'unixepoch'))       AS first_commit,
       max(date(author_unix, 'unixepoch'))       AS last_commit
FROM commits
GROUP BY author_name
ORDER BY commits DESC
LIMIT 15;
