-- Read the os-release file straight out of the layer tarball for a few distros.
-- Since /etc/os-release is usually a symlink, we read the real file at
-- /usr/lib/os-release. Selecting `content` makes the files table crack open just
-- this one file per image (path pushdown), not every file body. Newlines are
-- flattened so each release prints on a single row.
WITH refs(ref) AS (VALUES ('alpine'), ('debian'), ('ubuntu'))
SELECT refs.ref AS image,
       replace(trim(f.content), char(10), ' | ') AS os_release
FROM refs
JOIN files f ON f.reference = refs.ref AND f.path = '/usr/lib/os-release';
