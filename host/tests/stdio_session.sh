#!/bin/sh
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
# A stdio session driven from POSIX sh, no Python of its own: open a stream, read its id from the answer, read the
# head, close it, read the head again, send a line that is not JSON, then end the input and expect exit 0.
#   stdio_session.sh BIN DB ENGINES PRINCIPAL PROOF_URL
set -eu
bin=$1 db=$2 engines=$3 as=$4 proof=$5
dir=$(mktemp -d); trap 'rm -rf "$dir"' EXIT
mkfifo "$dir/in" "$dir/out"
"$bin" serve --stdio --db "$db" --engines "$engines" --as "$as" < "$dir/in" > "$dir/out" 2> "$dir/err" & pid=$!
exec 3> "$dir/in" 4< "$dir/out"
ask() { printf '%s\n' "$1" >&3; IFS= read -r answer <&4; }
expect() { case "$answer" in *"$1"*) ;; *) echo "stdio_session: expected $1 in: $answer" >&2; exit 1 ;; esac; }
ask '{"jsonrpc":"2.0","id":1,"method":"stream.open","params":{"proof_revision_url":"'"$proof"'"}}'; expect '"seq":0'
stream=$(printf '%s\n' "$answer" | sed -n 's/.*"stream_id":"\([0-9a-f-]*\)".*/\1/p')
ask '{"jsonrpc":"2.0","id":"h","method":"stream.head","params":{"stream_id":"'"$stream"'"}}'; expect '"length":1'
ask '{"jsonrpc":"2.0","id":2,"method":"stream.close","params":{"stream_id":"'"$stream"'"}}'
expect '"id":2,"result":{"seq":1'
ask '{"jsonrpc":"2.0","id":"h","method":"stream.head","params":{"stream_id":"'"$stream"'"}}'; expect '"length":2'
ask 'not json'; expect '{"jsonrpc":"2.0","id":null,"error":{"code":-32700'
exec 3>&-; wait "$pid" || { echo "stdio_session: exit $?" >&2; cat "$dir/err" >&2; exit 1; }
echo "stdio_session: ok $stream"
