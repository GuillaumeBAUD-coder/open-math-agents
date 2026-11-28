FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive
ARG TARGETARCH
ARG ELAN_VERSION=v4.4.0
ARG ELAN_SHA256_AMD64=0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2
ARG ELAN_SHA256_ARM64=45cde3006f82f98804c94cf2ca4949d117060a5f3cc8afa62f523759947ee21f
ARG FC_COMMIT=9097e2f90e66d2f6244209cb1c07f7120d17ec53

RUN apt-get update && apt-get install -y --no-install-recommends \
      bash \
      ca-certificates \
      coreutils \
      curl \
      findutils \
      git \
      grep \
      gzip \
      libgmp10 \
      python3 \
      sed \
      tar \
      zstd \
    && rm -rf /var/lib/apt/lists/*

# Use uid/gid 1001 to avoid colliding with Ubuntu 24.04's built-in uid 1000 ('ubuntu').
RUN groupadd -g 1001 oma && useradd -m -u 1001 -g 1001 -s /bin/bash oma

ENV ELAN_HOME=/opt/elan \
    OMA_FC=/opt/formal-conjectures \
    PATH=/opt/elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

# Install pinned elan release verified by SHA-256 for linux/amd64 or linux/arm64 (never curl | sh from a moving branch).
RUN arch="${TARGETARCH:-$(dpkg --print-architecture)}" \
    && case "$arch" in \
         amd64) target="x86_64-unknown-linux-gnu"; sha="$ELAN_SHA256_AMD64" ;; \
         arm64) target="aarch64-unknown-linux-gnu"; sha="$ELAN_SHA256_ARM64" ;; \
         *) echo "Unsupported TARGETARCH: $arch" >&2; exit 2 ;; \
       esac \
    && mkdir -p /opt/elan /tmp/elan-install \
    && curl -fsSL --retry 3 \
      "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-${target}.tar.gz" \
      -o /tmp/elan-install/elan.tar.gz \
    && printf '%s  %s\n' "$sha" /tmp/elan-install/elan.tar.gz | sha256sum -c - \
    && tar -xzf /tmp/elan-install/elan.tar.gz -C /tmp/elan-install \
    && /tmp/elan-install/elan-init -y --no-modify-path --default-toolchain none \
    && rm -rf /tmp/elan-install

# Check out pinned formal-conjectures, install toolchain, fetch Mathlib cache, and prebuild shared libraries.
RUN git init -q /opt/formal-conjectures \
    && git -C /opt/formal-conjectures remote add origin https://github.com/google-deepmind/formal-conjectures \
    && git -C /opt/formal-conjectures fetch -q --depth 1 origin "${FC_COMMIT}" \
    && git -C /opt/formal-conjectures checkout -q FETCH_HEAD \
    && cd /opt/formal-conjectures \
    && elan toolchain install "$(cat lean-toolchain)" \
    && for i in 1 2 3 4; do lake exe cache get && break; echo "cache retry $i"; sleep $((i * 15)); done \
    && lake build FormalConjecturesUtil FormalConjecturesForMathlib \
    && lake build --no-build FormalConjecturesUtil FormalConjecturesForMathlib \
    && chmod -R a+rX /opt/elan \
    && chown -R oma:oma /opt/formal-conjectures

USER oma
WORKDIR /work
