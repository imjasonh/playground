-- Commit activity by weekday (0 = Sunday) in the author's local time
SELECT CASE strftime('%w', author_when)
         WHEN '0' THEN 'Sun' WHEN '1' THEN 'Mon' WHEN '2' THEN 'Tue'
         WHEN '3' THEN 'Wed' WHEN '4' THEN 'Thu' WHEN '5' THEN 'Fri'
         WHEN '6' THEN 'Sat' END    AS weekday,
       count(*)                     AS commits
FROM commits
GROUP BY strftime('%w', author_when)
ORDER BY strftime('%w', author_when);
