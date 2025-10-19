#!/bin/bash

# Author: Juan Carlos Recio Abad
# Date: 2025-10-19

set -e

if [ -z "$1" ]; then
    echo "Usage: docker run <image> <github-repo-url>"
    exit 1
fi

REPO_URL=$1
REPO_NAME=$(basename "$REPO_URL" .git)

echo "========================================="
echo "Daikon JML Instrumentation Pipeline"
echo "========================================="
echo "Repository: $REPO_URL"
echo ""

# Step 1: Clone repository
echo "[1/7] Cloning repository..."
git clone "$REPO_URL" "$REPO_NAME"
cd "$REPO_NAME"

# Step 2: Check compilation
echo "[2/7] Checking compilation..."
if ! mvn clean compile; then
    echo "ERROR: Project compilation failed!"
    exit 1
fi
echo "✓ Project compiles successfully"

# Step 3: Detect test classes
echo "[3/7] Detecting test classes and their targets..."
python3 /usr/local/bin/process_project.py detect-tests
if [ ! -f "test-mapping.json" ]; then
    echo "ERROR: Failed to detect test classes"
    exit 1
fi

# Step 4: Compile tests
echo "[4/7] Compiling tests..."
if ! mvn test-compile; then
    echo "ERROR: Test compilation failed!"
    exit 1
fi
echo "✓ Tests compiled successfully"

# Step 5: Instrument classes with Daikon
echo "[5/7] Instrumenting classes with Daikon..."
python3 /usr/local/bin/process_project.py instrument-daikon

# Step 6: Run tests with Daikon
echo "[6/7] Running tests with Daikon to collect invariants..."
python3 /usr/local/bin/process_project.py run-daikon

# Step 7: Decorate classes with JML
echo "[7/7] Decorating classes with JML annotations..."
python3 /usr/local/bin/process_project.py generate-jml

echo ""
echo "========================================="
echo "✓ Pipeline completed successfully!"
echo "========================================="
echo ""
echo "Instrumented classes are in: instrumented-classes/"
echo "JML decorated classes are in: jml-decorated-classes/"
echo "Daikon output files are in: daikon-output/"
echo ""