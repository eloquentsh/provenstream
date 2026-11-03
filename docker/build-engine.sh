#!/bin/sh
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
# Build a linux engine of REPO at COMMIT in Docker (Dockerfile.engine), extract it with a PROVENANCE.json (and
# THIRD_PARTY_NOTICES and LICENSE, which travel with every engine), and install it into docker/engines (the directory
# docker-compose mounts), never replacing one.
#
#   docker/build-engine.sh REPO COMMIT [PACKAGE] [REPO_URL]
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="${1:?usage: build-engine.sh REPO COMMIT [PACKAGE] [REPO_URL]}"; COMMIT="$(git -C "$REPO" rev-parse --verify "${2:?}^{commit}")"
PACKAGE="${3:-.}"; URL="${4:-$(git -C "$REPO" remote get-url origin 2>/dev/null || echo "file://$(cd "$REPO" && pwd)")}"
TREE="$(git -C "$REPO" rev-parse "$COMMIT^{tree}")"
TAG="$COMMIT-$(printf '%s' "$PACKAGE" | tr -c 'A-Za-z0-9_.-' '-')"   # one image per revision: a commit and a package
OUT="$(mktemp -d)"; trap 'rm -rf "$OUT"' EXIT
START=$(date +%s)
mkdir "$OUT/ctx"; git -C "$REPO" archive "$COMMIT" | tar -x -C "$OUT/ctx"     # the commit's files only
docker build -f "$HERE/Dockerfile.engine" --build-arg REVISION="$COMMIT" \
  --build-arg REPO_URL="$URL" --build-arg PACKAGE="$PACKAGE" -t "provenstream-engine:$TAG" "$OUT/ctx"
cid=$(docker create "provenstream-engine:$TAG")
docker cp -q "$cid:/engine" "$OUT/engine"; docker cp -q "$cid:/describe.json" "$OUT/describe.json"
docker cp -q "$cid:/lean-version" "$OUT/lean-version"
docker cp -q "$cid:/THIRD_PARTY_NOTICES" "$OUT/THIRD_PARTY_NOTICES"; docker cp -q "$cid:/LICENSE" "$OUT/LICENSE"
docker rm "$cid" >/dev/null
python3 - "$OUT" "$COMMIT" "$TREE" "$URL" "$PACKAGE" "$(cat "$OUT/ctx/$PACKAGE/lean-toolchain")" "$(($(date +%s) - START))" \
  "$(docker image inspect -f '{{.Id}}' "provenstream-engine:$TAG")" <<'PY'
import datetime, hashlib, json, os, sys
out, commit, tree, url, package, toolchain, secs, image = sys.argv[1:9]
d = json.load(open(os.path.join(out, "describe.json")))
eng = os.path.join(out, "engine")
pkg = os.path.normpath(package).replace(os.sep, "/")
pkg = "" if pkg == "." else pkg                      # a revision is a commit and a package path ("" the root)
key = commit + "/" + pkg if pkg else commit
proof_url = url.rstrip("/") + ("/tree/%s/%s" % (commit, pkg) if pkg else "/commit/" + commit)
json.dump({"revision": key, "commit": commit, "package": pkg, "repo_url": url, "proof_url": proof_url,
           "source": {"commit": commit, "tree": tree, "package": package},
           "toolchain": {"name": toolchain, "lean_version": open(os.path.join(out, "lean-version")).read().strip()},
           "builder": {"platform": "docker: Dockerfile.engine", "image": image},
           "engine": {"file": "engine", "sha256": hashlib.sha256(open(eng, "rb").read()).hexdigest(),
                      "bytes": os.path.getsize(eng)},
           "schema": d["schema"], "build_seconds": int(secs),
           "built_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")},
          open(os.path.join(out, "PROVENANCE.json"), "w"), indent=2, sort_keys=True)
PY
mkdir -p "$HERE/engines"
# install inside the host image (a linux engine runs there, not necessarily here)
docker build -q -f "$HERE/Dockerfile.host" -t provenstream-host "$HERE/.." >/dev/null
docker run --rm --network none -u "$(id -u)" -v "$OUT:/build:ro" -v "$HERE/engines:/engines" provenstream-host \
  install /build --engines /engines
