output "hostname" {
  description = "Public exe.dev hostname for the CheSSH VM"
  value       = exedev_vm.app.hostname
}

output "ssh_connection_command" {
  description = "Command to play CheSSH"
  value       = "ssh ${exedev_vm.app.hostname}"
}

output "image_ref" {
  description = "GHCR image digest deployed to the VM"
  value       = ko_build.app.image_ref
}
