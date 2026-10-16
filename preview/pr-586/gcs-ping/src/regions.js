// Cloud Storage regional XML/JSON hosts that resolved in DNS as of
// 2026-10-16, plus the global anycast endpoint. Location labels follow
// Google Cloud's public region names. us-east7's city is not in the
// 2024 Wikipedia table; keep the region id until a public city name is.
export const GLOBAL_ID = "global";

export const PING_BUCKET = "gcs-ping-nonexistent-bucket";

export const REGIONS = Object.freeze([
  { id: GLOBAL_ID, location: "Global anycast" },
  { id: "africa-south1", location: "Johannesburg" },
  { id: "asia-east1", location: "Taiwan" },
  { id: "asia-east2", location: "Hong Kong" },
  { id: "asia-northeast1", location: "Tokyo" },
  { id: "asia-northeast2", location: "Osaka" },
  { id: "asia-northeast3", location: "Seoul" },
  { id: "asia-south1", location: "Mumbai" },
  { id: "asia-south2", location: "Delhi" },
  { id: "asia-southeast1", location: "Singapore" },
  { id: "asia-southeast2", location: "Jakarta" },
  { id: "australia-southeast1", location: "Sydney" },
  { id: "australia-southeast2", location: "Melbourne" },
  { id: "europe-central2", location: "Warsaw" },
  { id: "europe-north1", location: "Finland" },
  { id: "europe-north2", location: "Stockholm" },
  { id: "europe-southwest1", location: "Madrid" },
  { id: "europe-west1", location: "Belgium" },
  { id: "europe-west2", location: "London" },
  { id: "europe-west3", location: "Frankfurt" },
  { id: "europe-west4", location: "Netherlands" },
  { id: "europe-west6", location: "Zurich" },
  { id: "europe-west8", location: "Milan" },
  { id: "europe-west9", location: "Paris" },
  { id: "europe-west10", location: "Berlin" },
  { id: "europe-west12", location: "Turin" },
  { id: "me-central1", location: "Doha" },
  { id: "me-central2", location: "Dammam" },
  { id: "me-west1", location: "Tel Aviv" },
  { id: "northamerica-northeast1", location: "Montreal" },
  { id: "northamerica-northeast2", location: "Toronto" },
  { id: "northamerica-south1", location: "Querétaro" },
  { id: "southamerica-east1", location: "Sao Paulo" },
  { id: "southamerica-west1", location: "Santiago" },
  { id: "us-central1", location: "Iowa" },
  { id: "us-east1", location: "South Carolina" },
  { id: "us-east4", location: "Northern Virginia" },
  { id: "us-east5", location: "Columbus" },
  { id: "us-east7", location: "us-east7" },
  { id: "us-south1", location: "Dallas" },
  { id: "us-west1", location: "Oregon" },
  { id: "us-west2", location: "Los Angeles" },
  { id: "us-west3", location: "Salt Lake City" },
  { id: "us-west4", location: "Las Vegas" },
  { id: "us-west8", location: "Phoenix" },
]);

export function hostFor(regionId) {
  if (regionId === GLOBAL_ID) {
    return "storage.googleapis.com";
  }
  return `storage.${regionId}.rep.googleapis.com`;
}

export function pingUrl(regionId, nonce) {
  return `https://${hostFor(regionId)}/${PING_BUCKET}/${nonce}`;
}
