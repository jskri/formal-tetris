#!/usr/bin/env bash
set -euo pipefail

echo -n "1/8. Making rocq user the file owner... "
sudo chown -R 1000:1000 . # rocq user
trap 'echo -n "8/8. Restoring file ownership... " && \
  sudo chown -R "$(id -u)":"$(id -g)" . && \
  echo "done."' EXIT
echo "done."
echo ""

docker run --rm -v "$PWD":/workspace -w /workspace formal-tetris-ci:latest \
  bash -c "\
  echo '2/8. Rocq: checking proofs...' && \
  dune build --display=progress --action-stdout-on-success=swallow --action-stderr-on-success=must-be-empty && \
  echo 'Rocq: checking proofs: OK.' && \
  echo '' && \
  \
  cd js && \
  \
  echo '3/8. JS: installing dependencies...' && \
  npm ci && \
  echo '3/8. JS: installing dependencies: OK.' \
  echo '' && \
  \
  echo '4/8. JS: checking format...' && \
  npm run format:check && \
  echo '4/8. JS: checking format: OK.' \
  echo '' && \
  \
  echo '5/8. JS: linting...' && \
  npm run lint && \
  echo '5/8. JS: linting: OK.' \
  echo '' && \
  \
  echo '6/8. JS: checking syntax...' && \
  npm run syntax-check && \
  echo '6/8. JS: checking syntax: OK.' \
  echo '' && \
  \
  echo '7/8. JS: testing...' && \
  npm install && npm test && \
  echo '7/8. JS: testing: OK.'"

