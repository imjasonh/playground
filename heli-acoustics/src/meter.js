// RMS energy of one channel of an AudioBuffer. Pure enough for node --test.
export function channelRms(buffer, channel = 0) {
  const data = buffer.getChannelData(channel);
  let sum = 0;
  for (let i = 0; i < data.length; i++) sum += data[i] * data[i];
  return Math.sqrt(sum / data.length);
}

// Signed balance in [-1, +1]: negative = louder left, positive = louder right.
export function stereoBalance(leftRms, rightRms) {
  const total = leftRms + rightRms;
  if (total === 0) return 0;
  return (rightRms - leftRms) / total;
}
