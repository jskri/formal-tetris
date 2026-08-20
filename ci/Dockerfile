FROM rocq/rocq-prover:9.1

# rocq/rocq-prover is Debian 12 + opam 2.x, with a sudo, non-root user
# (uid/gid 1000) and one opam switch already containing Rocq and dune.
# Source: https://github.com/rocq-community/docker-base

# The base image sets SHELL to a login bash (to auto-load the opam env in
# interactive containers), which is inherited by RUN here too. A login
# shell sources /etc/profile, which unconditionally overwrites PATH — so
# it silently discards any PATH set via ENV below. Reset to a plain shell
# so ENV PATH additions (e.g. Rust's cargo/bin) actually take effect.
SHELL ["/bin/sh", "-c"]

USER root

# Node.js
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && curl -fsSL https://deb.nodesource.com/setup_24.x | bash - \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/*

USER rocq

# Rocq
RUN opam update && opam install -y coq coq-hammer-tactics.1.3.2+9.1

# Rust
ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$PATH \
    RUST_VERSION=1.97.1

USER root

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        gcc libc6-dev pkg-config \
        libx11-dev libxi-dev libgl1-mesa-dev libasound2-dev libudev-dev \
    && rm -rf /var/lib/apt/lists/* \
    && arch="$(dpkg --print-architecture)" \
    && case "$arch" in \
        'amd64') \
            rustArch='x86_64-unknown-linux-gnu'; \
            rustupSha256='4acc9acc76d5079515b46346a485974457b5a79893cfb01112423c89aeb5aa10'; \
            ;; \
        'armhf') \
            rustArch='armv7-unknown-linux-gnueabihf'; \
            rustupSha256='124e02253af9128f9e27ea1ac929cbb73cf44cf35469d0f594a1b62f7b71fea1'; \
            ;; \
        'arm64') \
            rustArch='aarch64-unknown-linux-gnu'; \
            rustupSha256='9732d6c5e2a098d3521fca8145d826ae0aaa067ef2385ead08e6feac88fa5792'; \
            ;; \
        'i386') \
            rustArch='i686-unknown-linux-gnu'; \
            rustupSha256='5140e82096f96d1d8077f00eb312648e0e5106d101c9918d086f72cbc69bb3a1'; \
            ;; \
        'ppc64el') \
            rustArch='powerpc64le-unknown-linux-gnu'; \
            rustupSha256='4bfff85bd3967d988e14567aa9cc6ab0ea386f0ffeff0f9f14d23f0103bf1f97'; \
            ;; \
        's390x') \
            rustArch='s390x-unknown-linux-gnu'; \
            rustupSha256='66c2c132428b6b77803facb02cbdf33b89d20c00bd20da142be8cb651f2e7cd8'; \
            ;; \
        'riscv64') \
            rustArch='riscv64gc-unknown-linux-gnu'; \
            rustupSha256='7e43f2b2e6307d61da17a4dff61e6bceef408b8189822df64e1094590d2a70f9'; \
            ;; \
        *) \
            echo >&2 "unsupported architecture: $arch"; \
            exit 1; \
            ;; \
      esac \
    && url="https://static.rust-lang.org/rustup/archive/1.29.0/${rustArch}/rustup-init" \
    && curl -O "$url" \
    && echo "${rustupSha256} *rustup-init" | sha256sum -c - \
    && chmod +x rustup-init \
    && ./rustup-init -y --no-modify-path --profile default --default-toolchain $RUST_VERSION --default-host ${rustArch} \
    && rm rustup-init \
    && chmod -R a+w $RUSTUP_HOME $CARGO_HOME \
    && rustup --version \
    && cargo --version \
    && rustc --version \
    && cargo clippy --version \
    && cargo fmt --version

USER rocq

WORKDIR /workspace
