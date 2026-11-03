# Phase 2: remote build on demand (not built)

Today an operator builds and installs each engine (`provenstream engine build`, `engine install`). Phase 2 lets a host
build the engine of a revision (a commit and a package) the first time a `stream.open` names it. Its design, so that
it adds no trust it cannot state:

- **Allowlist**: the host builds only from repositories on an operator list (URL prefixes), never from an arbitrary
  URL in a request. Anything else stays `revision_must_be_installed`.
- **Pending state**: an opening naming an allowed but unbuilt revision is answered `pending` with nothing stored; the
  client retries. The stream does not exist until an engine of its revision decides its opening. A build failure is
  recorded and answered `revision_must_be_installed` with the build log's reason.
- **Sandbox**: the build runs in a container without network except the toolchain and the repository fetch (both
  pinned: the commit by hash, the toolchain by digest from `toolchains.json`), with CPU, memory, disk and time limits,
  no host secrets, and an unprivileged user. The resulting engine runs under the same limits (seccomp, no network).
- **Provenance**: the manifest records the build's inputs as `provenstream build` does, plus the sandbox image digest;
  the host publishes manifests so anyone can rebuild and compare (`provenstream verify`).
- **Never replace**: as for manual installs, a built revision is final.

What phase 2 would not change: the proofs, the engine protocol, routing, or what a stream guarantees.
