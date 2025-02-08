FROM ubuntu:24.04

LABEL maintainer="codinuum"

RUN set -x && \
    mkdir -p /opt/cca && \
    mkdir -p /var/lib/cca && \
    useradd -r -d /opt/cca -s /bin/nologin cca && \
    chown -R cca:cca /opt/cca && \
    chown -R cca:cca /var/lib/cca

RUN set -x && \
    cd /root && \
    apt-get update && \
    apt-get upgrade -y && \
    env DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        libgmp-dev pkg-config zlib1g-dev \
        ca-certificates \
        git \
        mercurial \
        opam

RUN set -x && \
    cd /root && \
    opam init -y --disable-sandboxing --bare && \
    eval $(opam env) && \
    opam update && \
    opam switch create 5.3.0+flambda ocaml-variants.5.3.0+options ocaml-option-flambda && \
    eval $(opam env --switch=5.3.0) && \
    echo 'test -r /root/.opam/opam-init/init.sh && . /root/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true' >> .bashrc && \
    echo 'export PATH=/opt/cca/bin:${PATH}' >> .bashrc

RUN set -x && \
    cd /root && \
    mkdir diffast && \
    opam update && \
    opam upgrade -y && \
    eval $(opam env) && \
    opam install -y bytesrw camlp-streams camlzip cryptokit csv dune dune-site git-unix markup menhir sedlex uuidm vlt

COPY . /root/diffast

RUN set -x && \
    cd /root/diffast && \
    opam update && \
    opam upgrade -y && \
    eval $(opam env) && \
    dune build && \
    dune install --relocatable --prefix dist && \
    dune clean

RUN set -x && \
    ln -s /root/diffast/dist/bin /opt/cca/bin

RUN set -x && \
    apt-get autoremove -y && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

CMD ["/bin/bash"]
