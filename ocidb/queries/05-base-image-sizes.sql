-- Compare common base images by compressed download size (linux/amd64).
-- The reference is pushed down into the virtual table once per CTE row, so this
-- single query fetches four separate images straight from Docker Hub.
WITH refs(ref) AS (VALUES ('alpine'), ('busybox'), ('debian'), ('ubuntu'))
SELECT refs.ref AS image,
       i.num_layers,
       printf('%.2f MB', i.total_size / 1048576.0) AS download_size
FROM refs
JOIN image i ON i.reference = refs.ref
ORDER BY i.total_size;
