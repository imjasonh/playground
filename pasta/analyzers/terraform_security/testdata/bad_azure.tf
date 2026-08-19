resource "azurerm_storage_account" "http" { # want "allows HTTP"
  enable_https_traffic_only = false
}

resource "azurerm_network_security_rule" "ssh" { # want "allows SSH (22) from any source"
  access                 = "Allow"
  direction              = "Inbound"
  destination_port_range = "22"
  source_address_prefix  = "*"
}
