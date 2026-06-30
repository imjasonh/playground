-- Reverse-engineer the "Dockerfile": the build steps that created each
-- non-empty layer of the alpine image.
SELECT ordinal, created_by
FROM history
WHERE reference = 'alpine'
  AND empty_layer = 0;
