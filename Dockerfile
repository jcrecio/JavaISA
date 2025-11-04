FROM ubuntu:22.04

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies
RUN apt-get update && apt-get install -y \
    wget \
    git \
    openjdk-8-jdk \
    maven \
    python3 \
    python3-pip \
    unzip \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Set JAVA_HOME
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
ENV PATH="${JAVA_HOME}/bin:${PATH}"

# Install Daikon
WORKDIR /opt
RUN wget https://plse.cs.washington.edu/daikon/download/daikon-5.8.22.tar.gz && \
    tar -xzf daikon-5.8.22.tar.gz && \
    rm daikon-5.8.22.tar.gz

ENV DAIKONDIR=/opt/daikon-5.8.22
ENV PATH="${DAIKONDIR}/bin:${PATH}"
ENV CLASSPATH="${DAIKONDIR}/daikon.jar:${CLASSPATH}"

# Compile Daikon
WORKDIR ${DAIKONDIR}
RUN make -j$(nproc) || make

# Try to build DynComp runtime (dcomp_rt.jar)
# This may fail, but we'll make it optional
RUN echo "Attempting to build DynComp runtime..." && \
    (cd java && make dcomp_rt.jar) || \
    echo "Warning: DynComp runtime not built. DynComp will be disabled."

# Verify Daikon installation
RUN test -f ${DAIKONDIR}/daikon.jar || (echo "ERROR: daikon.jar not found!" && exit 1)
RUN java -cp ${DAIKONDIR}/daikon.jar daikon.Daikon --help | head -5 || echo "Daikon installed"

# Check if DynComp is available
RUN if [ -f ${DAIKONDIR}/java/dcomp_rt.jar ]; then \
        echo "✓ DynComp runtime available"; \
    else \
        echo "⚠ DynComp runtime not available - will run without comparability analysis"; \
    fi

# Copy scripts to the image
COPY entrypoint.sh /usr/local/bin/entrypoint.sh
COPY process_project.py /usr/local/bin/process_project.py

# Make scripts executable
RUN chmod +x /usr/local/bin/entrypoint.sh && \
    chmod +x /usr/local/bin/process_project.py

# Create working directory
WORKDIR /workspace

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]