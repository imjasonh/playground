-- When were these images built, and with what tooling?
WITH refs(ref) AS (VALUES ('nginx'), ('redis'), ('postgres'))
SELECT refs.ref AS image,
       i.created,
       i.docker_version
FROM refs
JOIN image i ON i.reference = refs.ref
ORDER BY i.created DESC;
