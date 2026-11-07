/**
 * Pad one prepared Laya question into a rectangular batch, the way
 * `collate_items` does. Batch size is the number of questions in the call.
 */
export function collateItems(items, padId) {
  if (items.length === 0) {
    throw new Error("systemOne: at least one question is required");
  }
  const length = Math.max(...items.map((item) => item.ids.length));
  const maxOptions = Math.max(...items.map((item) => item.markers.length));
  const n = items.length;
  const inputIds = new BigInt64Array(n * length).fill(BigInt(padId));
  const attention = new BigInt64Array(n * length);
  const markerPos = new BigInt64Array(n * maxOptions);
  const markerMask = new Uint8Array(n * maxOptions);
  const qtype = new BigInt64Array(n);
  let tokenCount = 0;
  items.forEach((item, row) => {
    item.ids.forEach((id, column) => {
      inputIds[row * length + column] = BigInt(id);
      attention[row * length + column] = 1n;
    });
    tokenCount += item.ids.length;
    item.markers.forEach((position, column) => {
      markerPos[row * maxOptions + column] = BigInt(position);
      markerMask[row * maxOptions + column] = 1;
    });
    qtype[row] = BigInt(item.qtype);
  });
  return {
    n,
    length,
    maxOptions,
    inputIds,
    attention,
    markerPos,
    markerMask,
    qtype,
    tokenCount,
  };
}

export function collateToShape(item, shape, padId) {
  if (item.markers.length > shape.maxOptions) {
    throw new Error(
      `${item.markers.length} options, but this export supports at most ${shape.maxOptions}.`,
    );
  }
  if (item.ids.length > shape.maxLength) {
    throw new Error(
      `Input has ${item.ids.length} tokens, but this export supports at most ${shape.maxLength}.`,
    );
  }
  const inputIds = Array(shape.maxLength).fill(padId);
  const attention = Array(shape.maxLength).fill(false);
  attention[0] = true;
  item.ids.forEach((id, index) => {
    inputIds[index] = id;
    attention[index] = true;
  });
  const markerPositions = Array(shape.maxOptions).fill(0);
  const markerMask = Array(shape.maxOptions).fill(false);
  item.markers.forEach((position, index) => {
    markerPositions[index] = position;
    markerMask[index] = true;
  });
  return {
    inputIds,
    attentionMask: attention,
    markerPositions,
    markerMask,
    kind: item.kind,
    tokenCount: item.ids.length,
    optionCount: item.markers.length,
  };
}
