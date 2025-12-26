# Dockerfile for μACP Formal Verification Environment
# Provides TLA+ Tools (TLC) and Coq with specific versions

FROM ubuntu:22.04

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y \
    wget \
    curl \
    unzip \
    openjdk-17-jdk \
    build-essential \
    git \
    && rm -rf /var/lib/apt/lists/*

# Install Coq 8.17.1
# Using opam (OCaml package manager) for Coq installation
RUN apt-get update && apt-get install -y \
    opam \
    pkg-config \
    libgmp-dev \
    libnum-ocaml-dev \
    && rm -rf /var/lib/apt/lists/*

# Initialize opam and install Coq 8.17.1
RUN opam init --disable-sandboxing -y
RUN eval $(opam env) && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam install -y coq.8.17.1

# Add opam environment to PATH and ensure it's available
ENV PATH="/root/.opam/default/bin:${PATH}"
ENV OPAM_SWITCH_PREFIX="/root/.opam/default"
ENV CAML_LD_LIBRARY_PATH="/root/.opam/default/lib/stublibs:/root/.opam/default/lib/ocaml/stublibs:/root/.opam/default/lib/ocaml"

# Install TLA+ Tools (TLC)
# Download TLA+ Tools jar file
RUN mkdir -p /opt/tla && \
    wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/TLAToolbox-1.8.0-linux.gtk.x86_64.zip -O /tmp/tla-toolbox.zip && \
    unzip -q /tmp/tla-toolbox.zip -d /opt/tla && \
    rm /tmp/tla-toolbox.zip || \
    (echo "Note: TLA+ Toolbox download may have failed. You can manually download from https://github.com/tlaplus/tlaplus/releases" && \
     echo "Alternatively, use TLC directly via Java with the tla2tools.jar")

# Alternative: Install TLC via tla2tools.jar (more reliable for CI)
RUN mkdir -p /opt/tla && \
    wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -O /opt/tla/tla2tools.jar || \
    echo "Note: tla2tools.jar download failed. Please download manually."

# Set up TLC environment
ENV CLASSPATH="/opt/tla/tla2tools.jar:${CLASSPATH}"
ENV TLA_TOOLBOX_HOME="/opt/tla"

# Create a wrapper script for TLC
RUN echo '#!/bin/bash\njava -cp /opt/tla/tla2tools.jar tlc2.TLC "$@"' > /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc

# Set working directory
WORKDIR /workspace

# Verify installations
RUN java -version
RUN eval $(opam env) && coqc --version

# Default command
CMD ["/bin/bash"]

