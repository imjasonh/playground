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

output "ssh_host_public_key" {
  description = "OpenSSH public key for the game SSH host key"
  value       = tls_private_key.ssh_host.public_key_openssh
}
