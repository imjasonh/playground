job "example" {
  datacenters = ["dc1"]

  group "web" {
    task "nginx" {
      driver = "docker"
    }
  }
}
