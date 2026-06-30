-- Cross-image search: which of these images actually ship bash? On usrmerge
-- distros /bin is a symlink to /usr/bin, so the real binary lives at
-- /usr/bin/bash. The correlated subquery binds `reference` per row and pushes
-- the exact `path`, so every lookup reads a single layer's table of contents
-- rather than scanning whole filesystems.
WITH refs(ref) AS (VALUES ('alpine'), ('busybox'), ('debian'), ('ubuntu'))
SELECT ref AS image,
       CASE WHEN EXISTS (
         SELECT 1 FROM files
         WHERE reference = refs.ref AND path = '/usr/bin/bash'
       ) THEN 'yes' ELSE 'no' END AS has_bash
FROM refs
ORDER BY ref;
