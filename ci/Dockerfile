FROM rocq/rocq-prover:9.1

# rocq/rocq-prover is Debian 12 + opam 2.x, with a sudo, non-root user
# (uid/gid 1000) and one opam switch already containing Rocq and dune.
# Source: https://github.com/rocq-community/docker-base
USER root
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && curl -fsSL https://deb.nodesource.com/setup_24.x | bash - \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/*

USER rocq
RUN opam update && opam install -y coq coq-hammer-tactics.1.3.2+9.1

WORKDIR /workspace
