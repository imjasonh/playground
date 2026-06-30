-- Most recent tags (releases), newest first
SELECT name,
       type,
       substr(target, 1, 10)  AS points_at,
       tagger_name,
       tagger_when
FROM tags
ORDER BY tagger_unix DESC NULLS LAST
LIMIT 20;
