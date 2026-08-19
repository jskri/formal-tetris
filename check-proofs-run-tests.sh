#!/usr/bin/env bash
set -euo pipefail

echo -n "1/4. Making rocq user the file owner... "
sudo chown -R 1000:1000 . # rocq user
trap 'echo -n "4/4. Restoring file ownership... " && \
  sudo chown -R "$(id -u)":"$(id -g)" . && \
  echo "done."' EXIT
echo "done."
echo ""

docker run --rm -v "$PWD":/workspace -w /workspace formal-tetris-ci \
  bash -c "\
  echo '2/4. Checking proofs...' && \
  dune build --display=progress --action-stdout-on-success=swallow --action-stderr-on-success=must-be-empty && \
  echo 'Checking proof: done.' && \
  echo '' && \
  echo '3/4. Running JS tests.' && \
  cd js && npm install && npm test && \
  echo 'Running JS tests: done.' && \
  echo ''"
