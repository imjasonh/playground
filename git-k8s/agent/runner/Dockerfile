# Builds the image that runs the agent in git-k8s agent Pods. The tests run
# during the build, and they need git, which the -dev image has.
ARG CHAINGUARD=cgr.dev/chainguard

FROM ${CHAINGUARD}/node:latest-dev AS build
WORKDIR /app
COPY --chown=65532:65532 package.json package-lock.json ./
RUN npm ci --ignore-scripts --no-audit --no-fund
COPY --chown=65532:65532 tsconfig.json tsconfig.build.json ./
COPY --chown=65532:65532 src ./src
COPY --chown=65532:65532 tests ./tests
RUN npm run typecheck && npm test && npm run build && npm prune --omit=dev --ignore-scripts --no-audit --no-fund

# @cursor/sdk installs a package for the build's platform, so both stages
# must have the same platform.
FROM ${CHAINGUARD}/node:latest
WORKDIR /app
COPY --from=build --chown=0:0 /app/package.json ./
COPY --from=build --chown=0:0 /app/node_modules ./node_modules
COPY --from=build --chown=0:0 /app/dist ./dist
ENTRYPOINT ["/usr/bin/node", "/app/dist/main.js"]
