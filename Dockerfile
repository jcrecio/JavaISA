FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

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
RUN make

# Create working directory
WORKDIR /workspace

# Copy the main script
COPY entrypoint.sh /usr/local/bin/entrypoint.sh
COPY process_project.py /usr/local/bin/process_project.py
RUN chmod +x /usr/local/bin/entrypoint.sh

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]