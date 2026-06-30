-- Hunt for files carrying special permission bits (setuid/setgid/sticky) in the
-- debian image. mode is rendered as octal, so a leading digit of 1-7 means a
-- special bit is set. This scans every path in the image but reads only the
-- tables of contents -- no file bodies -- so it stays cheap.
SELECT path, mode, size
FROM files
WHERE reference = 'debian'
  AND type = 'file'
  AND substr(mode, 1, 1) IN ('1', '2', '3', '4', '5', '6', '7')
ORDER BY mode DESC, path
LIMIT 25;
