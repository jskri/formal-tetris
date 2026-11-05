#!/usr/bin/env bash
set -euo pipefail

echo -n "1/12. Making rocq user the file owner... "
sudo chown -R 1000:1000 . # rocq user
trap 'echo -n "12/12. Restoring file ownership... " && \
  sudo chown -R "$(id -u)":"$(id -g)" . && \
  echo "done."' EXIT
echo "done."
echo ""

docker run --rm -v "$PWD":/workspace -w /workspace formal-tetris-ci:latest \
  bash -c "\
  echo '2/12. Rocq: checking proofs...' && \
  dune build --display=progress --action-stdout-on-success=swallow --action-stderr-on-success=must-be-empty && \
  echo '2/12. Rocq: checking proofs: OK.' && \
  echo '' && \
  \
  cd rs && \
  \
  echo '3/12. Rust: checking format...' && \
  cargo fmt --all -- --check && \
  echo '3/12. Rust: checking format: OK.' && \
  echo '' && \
  \
  echo '4/12. Rust: running clippy...' && \
  cargo clippy --workspace --all-targets -- -D warnings && \
  echo '4/12. Rust: running clippy: OK.' && \
  echo '' && \
  \
  echo '5/12. Rust: building...' && \
  cargo build --workspace --all-targets && \
  echo '5/12. Rust: building: OK.' && \
  echo '' && \
  \
  echo '6/12. Rust: testing...' && \
  cargo test --workspace && \
  echo '6/12. Rust: testing: OK.' && \
  echo '' && \
  \
  cd ../js && \
  \
  echo '7/12. JS: installing dependencies...' && \
  npm ci && \
  echo '7/12. JS: installing dependencies: OK.' && \
  echo '' && \
  \
  echo '8/12. JS: checking format...' && \
  npm run format:check && \
  echo '8/12. JS: checking format: OK.' && \
  echo '' && \
  \
  echo '9/12. JS: linting...' && \
  npm run lint && \
  echo '9/12. JS: linting: OK.' && \
  echo '' && \
  \
  echo '10/12. JS: checking syntax...' && \
  npm run syntax-check && \
  echo '10/12. JS: checking syntax: OK.' && \
  echo '' && \
  \
  echo '11/12. JS: testing...' && \
  npm test && \
  echo '11/12. JS: testing: OK.'"
