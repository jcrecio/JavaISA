#!/bin/bash

# Author: Juan Carlos Recio Abad
# Date: 2025-10-19

set -e

# Show usage
show_usage() {
    echo "Usage:"
    echo "  docker run <image> prepare <github-repo-url>   - Clone, compile, and detect tests"
    echo "  docker run <image> analyze <repo-name>         - Run Daikon analysis and generate JML"
    echo ""
    echo "Example workflow:"
    echo "  docker run -v \$(pwd)/workspace:/workspace <image> prepare https://github.com/user/repo.git"
    echo "  docker run -v \$(pwd)/workspace:/workspace <image> analyze repo"
}

if [ -z "$1" ]; then
    show_usage
    exit 1
fi

COMMAND=$1

case $COMMAND in
    prepare)
        if [ -z "$2" ]; then
            echo "ERROR: Repository URL required for 'prepare' command"
            show_usage
            exit 1
        fi

        REPO_URL=$2
        REPO_NAME=$(basename "$REPO_URL" .git)

        echo "========================================="
        echo "Daikon JML - PREPARE Phase"
        echo "========================================="
        echo "Repository: $REPO_URL"
        echo ""

        # Step 1: Clone repository
        echo "[1/4] Cloning repository..."
        if [ -d "$REPO_NAME" ]; then
            echo "Repository directory already exists, using existing clone..."
            cd "$REPO_NAME"
            git pull || echo "Warning: Could not pull latest changes"
        else
            git clone "$REPO_URL" "$REPO_NAME"
            cd "$REPO_NAME"
        fi

        # Step 2: Check compilation
        echo "[2/4] Checking compilation..."
        if ! mvn clean compile; then
            echo "ERROR: Project compilation failed!"
            exit 1
        fi
        echo "✓ Project compiles successfully"

        # Step 3: Detect test classes
        echo "[3/4] Detecting test classes and their targets..."
        python3 /usr/local/bin/process_project.py detect-tests
        if [ ! -f "test-mapping.json" ]; then
            echo "ERROR: Failed to detect test classes"
            exit 1
        fi

        # Step 4: Compile tests
        echo "[4/4] Compiling tests..."
        if ! mvn test-compile; then
            echo "ERROR: Test compilation failed!"
            exit 1
        fi
        echo "✓ Tests compiled successfully"

        echo ""
        echo "========================================="
        echo "✓ PREPARE phase completed successfully!"
        echo "========================================="
        echo ""
        echo "Test mapping saved to: test-mapping.json"
        echo ""
        echo "Next step: Run analysis with:"
        echo "  docker run -v \$(pwd)/workspace:/workspace <image> analyze $REPO_NAME"
        echo ""
        ;;

    analyze)
        if [ -z "$2" ]; then
            echo "ERROR: Repository name required for 'analyze' command"
            show_usage
            exit 1
        fi

        REPO_NAME=$2

        if [ ! -d "$REPO_NAME" ]; then
            echo "ERROR: Repository directory '$REPO_NAME' not found!"
            echo "Have you run 'prepare' first?"
            exit 1
        fi

        cd "$REPO_NAME"

        if [ ! -f "test-mapping.json" ]; then
            echo "ERROR: test-mapping.json not found!"
            echo "Please run 'prepare' command first."
            exit 1
        fi

        echo "========================================="
        echo "Daikon JML - ANALYZE Phase"
        echo "========================================="
        echo "Repository: $REPO_NAME"
        echo ""

        # Step 5: Instrument classes with Daikon
        echo "[1/3] Instrumenting classes with Daikon..."
        python3 /usr/local/bin/process_project.py instrument-daikon

        # Step 6: Run tests with Daikon
        echo "[2/3] Running tests with Daikon to collect invariants..."
        echo "This may take a while depending on the number of tests..."
        echo "---> $REPO_NAME"
        python3 /usr/local/bin/process_project.py run-daikon
        # Step 7: Decorate classes with JML
        echo "[3/3] Decorating classes with JML annotations..."
        python3 /usr/local/bin/process_project.py generate-jml

        echo ""
        echo "========================================="
        echo "✓ ANALYZE phase completed successfully!"
        echo "========================================="
        echo ""
        echo "Results:"
        echo "  - Daikon output files: daikon-output/"
        echo "  - JML decorated classes: jml-decorated-classes/"
        echo "  - Instrumentation info: instrumented-classes/"
        echo ""
        ;;

    *)
        echo "ERROR: Unknown command '$COMMAND'"
        show_usage
        exit 1
        ;;
esac