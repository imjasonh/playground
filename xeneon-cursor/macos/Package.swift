// swift-tools-version: 5.9
import PackageDescription

let package = Package(
  name: "XeneonCursor",
  platforms: [
    .macOS(.v13),
  ],
  products: [
    .executable(name: "XeneonCursor", targets: ["XeneonCursor"]),
  ],
  targets: [
    .executableTarget(
      name: "XeneonCursor",
      path: "Sources/XeneonCursor",
      exclude: ["Bridge.js"]
    ),
  ]
)
