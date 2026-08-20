#!/usr/bin/env bash
set -euo pipefail

echo -n "1/11. Making rocq user the file owner... "
sudo chown -R 1000:1000 . # rocq user
trap 'echo -n "11/11. Restoring file ownership... " && \
  sudo chown -R "$(id -u)":"$(id -g)" . && \
  echo "done."' EXIT
echo "done."
echo ""

docker run --rm -v "$PWD":/workspace -w /workspace formal-tetris-ci:latest \
  bash -c "\
  echo '2/11. Rocq: checking proofs...' && \
  dune build --display=progress --action-stdout-on-success=swallow --action-stderr-on-success=must-be-empty && \
  echo 'Rocq: checking proofs: OK.' && \
  echo '' && \
  \
  cd rs && \
  \
  echo '3/11. Rust: running clippy...' && \
  cargo clippy --workspace --all-targets -- -D warnings && \
  echo '3/11. Rust: running clippy: OK.' && \
  echo '' && \
  \
  echo '4/11. Rust: building...' && \
  cargo build --workspace --all-targets && \
  echo '4/11. Rust: building: OK.' && \
  echo '' && \
  \
  echo '5/11. Rust: testing...' && \
  cargo test --workspace && \
  echo '5/11. Rust: testing: OK.' && \
  echo ''
  \
  cd ../js && \
  \
  echo '6/11. JS: installing dependencies...' && \
  npm ci && \
  echo '6/11. JS: installing dependencies: OK.' \
  echo '' && \
  \
  echo '7/11. JS: checking format...' && \
  npm run format:check && \
  echo '7/11. JS: checking format: OK.' \
  echo '' && \
  \
  echo '8/11. JS: linting...' && \
  npm run lint && \
  echo '8/11. JS: linting: OK.' \
  echo '' && \
  \
  echo '9/11. JS: checking syntax...' && \
  npm run syntax-check && \
  echo '9/11. JS: checking syntax: OK.' \
  echo '' && \
  \
  echo '10/11. JS: testing...' && \
  npm install && npm test && \
  echo '10/11. JS: testing: OK.'"

