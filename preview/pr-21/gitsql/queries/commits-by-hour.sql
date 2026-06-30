-- When do people commit? Commits bucketed by hour of the author's local clock
SELECT strftime('%H', author_when) AS hour,
       count(*)                    AS commits
FROM commits
GROUP BY hour
ORDER BY hour;
