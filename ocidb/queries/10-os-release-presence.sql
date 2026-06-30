-- Where does /etc/os-release live across base images? On modern distros it is a
-- symlink into /usr/lib, while busybox does not ship it at all (and so drops out
-- of the join). Equality on `path` is pushed into the files table, so each image
-- is probed for just this one entry -- only the layer table of contents is read.
WITH refs(ref) AS (VALUES ('alpine'), ('busybox'), ('debian'), ('ubuntu'))
SELECT refs.ref AS image,
       f.type,
       coalesce(f.linkname, '(regular file)') AS target
FROM refs
JOIN files f ON f.reference = refs.ref AND f.path = '/etc/os-release'
ORDER BY refs.ref;
