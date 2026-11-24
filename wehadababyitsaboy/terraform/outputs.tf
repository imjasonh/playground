output "url" {
  description = "Base URL that clients request. Append CLIENT/ARGS?bob=wehadababyitsaboy."
  value       = "https://storage.googleapis.com/${google_storage_bucket.pixel.name}/"
}

output "logs_bucket" {
  description = "Bucket that holds the hourly usage log CSVs."
  value       = google_storage_bucket.logs.name
}
