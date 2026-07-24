FROM ubuntu:22.04

ARG DEBIAN_FRONTEND=noninteractive
SHELL ["/bin/bash", "-eo", "pipefail", "-c"]

RUN apt-get update && apt-get install -y --no-install-recommends \
      curl ca-certificates git && \
    rm -rf /var/lib/apt/lists/*

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
      bash -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:$PATH"

WORKDIR /mgql
COPY lean-toolchain lakefile.lean lake-manifest.json MGQL.lean ./
COPY MGQL/ MGQL/
COPY verify-soundness.sh run-test.sh HOWTO.md README.md LICENSE ./
RUN chmod +x verify-soundness.sh run-test.sh

RUN lake build
RUN lake build ldbcBench

CMD ["./verify-soundness.sh"]
