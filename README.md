# JavaISA: Daikon JML Instrumentation Docker Tool

A comprehensive Docker-based tool for automatically modelling JML specifications from Java Maven projects using the Daikon invariant detector.

## Table of Contents

- [Overview](#overview)
- [What This Tool Does](#what-this-tool-does)
- [Prerequisites](#prerequisites)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Two-Phase Workflow](#two-phase-workflow)
- [Detailed Command Reference](#detailed-command-reference)
- [Pipeline Architecture](#pipeline-architecture)
- [Output Structure](#output-structure)
- [Examples](#examples)
- [Advanced Usage](#advanced-usage)
- [Troubleshooting](#troubleshooting)
- [Technical Details](#technical-details)
- [Limitations](#limitations)
- [FAQ](#faq)
- [Contributing](#contributing)
- [License](#license)

## Overview

This Docker image provides a complete, automated pipeline for:
- Analyzing Java projects to understand their test structure
- Running Daikon to infer program invariants from test executions
- Generating formal JML specifications based on discovered invariants
- Decorating original source code with JML annotations

The tool uses a **two-phase approach** for better control and flexibility:
1. **Prepare Phase**: Fast setup (clone, compile, detect tests)
2. **Analyze Phase**: Intensive analysis (Daikon instrumentation and JML generation)

## What This Tool Does

### The Two-Phase Process

#### Phase 1: Prepare (Fast - 1-5 minutes)
1. **Repository Cloning**: Downloads your Java project from GitHub
2. **Compilation Verification**: Ensures the project builds successfully with Maven
3. **Test Discovery**: Intelligently identifies all JUnit test classes (both JUnit 4 and 5)
4. **Test Mapping**: Analyzes test code to determine which production classes each test exercises

#### Phase 2: Analyze (Intensive - 10-60 minutes)
5. **Daikon Instrumentation**: Instruments bytecode to collect runtime information
6. **Invariant Collection**: Runs your test suite while recording variable values and relationships
7. **JML Generation**: Converts discovered invariants into formal JML specifications
8. **Code Decoration**: Adds JML specifications as comments to your original source files

### What Are Invariants?

Invariants are properties that always hold true during program execution. Daikon discovers invariants like:

- **Variable relationships**: `x > y`, `array.length == count`
- **Object properties**: `field != null`, `list.isEmpty() == false`
- **Method behaviors**: Return values, parameter constraints
- **Class invariants**: Properties that hold for all instances

### What Is JML?

JML (Java Modeling Language) is a specification language for Java that allows you to formally describe:
- Preconditions (what must be true before a method executes)
- Postconditions (what will be true after a method executes)
- Invariants (what's always true for a class)
- Exceptional behavior

## Prerequisites

### Required Software

- **Docker**: Version 20.10 or higher
  - [Install Docker on Linux](https://docs.docker.com/engine/install/)
  - [Install Docker Desktop on Mac](https://docs.docker.com/desktop/install/mac-install/)
  - [Install Docker Desktop on Windows](https://docs.docker.com/desktop/install/windows-install/)

### Project Requirements

Your Java project must meet these criteria:

- **Version Control**: Hosted on GitHub (public or accessible with credentials)
- **Build System**: Uses Apache Maven with a valid `pom.xml`
- **Java Version**: Compatible with Java 8
- **Testing Framework**: Uses JUnit 4.x or JUnit 5.x
- **Project Structure**: Follows standard Maven directory layout:
  ```
  project/
  ├── pom.xml
  └── src/
      ├── main/java/       # Production code
      └── test/java/       # Test code
  ```
- **Runnable Tests**: Tests should execute successfully with `mvn test`

## Installation

### Building the Docker Image

1. **Create or download these files** to a directory:
   - `Dockerfile`
   - `entrypoint.sh`
   - `process_project.py`

2. **Navigate to the directory**:
   ```bash
   cd /path/to/docker-files
   ```

3. **Build the Docker image**:
   ```bash
   docker build -t daikon-jml:latest .
   ```

   This process takes 10-20 minutes as it:
   - Downloads Ubuntu base image
   - Installs Java 8 and Maven
   - Downloads Daikon (5.8.18)
   - Compiles Daikon from source

4. **Verify the build**:
   ```bash
   docker images | grep daikon-jml
   ```

   You should see output like:
   ```
   daikon-jml    latest    abc123def456    5 minutes ago    2.5GB
   ```

## Quick Start

### Complete Two-Phase Workflow

```bash
# Create workspace directory
mkdir -p workspace

# Phase 1: Prepare the project (fast)
docker run --rm \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/username/repository.git

# Phase 2: Run Daikon analysis (slow)
docker run --rm \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze repository
```

**Windows PowerShell:**
```powershell
# Create workspace directory
New-Item -ItemType Directory -Force -Path workspace

# Phase 1: Prepare
docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  prepare https://github.com/username/repository.git

# Phase 2: Analyze
docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  analyze repository
```

### Check Results

After both phases complete:

```bash
# View test mapping
cat workspace/repository/test-mapping.json

# List Daikon outputs
ls workspace/repository/daikon-output/

# View JML decorated classes
ls workspace/repository/jml-decorated-classes/
```

## Two-Phase Workflow

### Why Two Phases?

The split workflow provides several advantages:

**Benefits:**

1. ✅ **Verify Compilation First**: Ensure the project compiles before running time-consuming Daikon analysis
2. ✅ **Inspect Test Mapping**: Review `test-mapping.json` to see what will be analyzed
3. ✅ **Modify Configuration**: Adjust test selection between phases
4. ✅ **Resume Analysis**: If analysis fails, re-run only the analyze phase
5. ✅ **Batch Processing**: Prepare multiple projects, analyze them later or in parallel
6. ✅ **Resource Management**: Run prepare on local machine, analyze on powerful server

### Typical Workflow

```
┌─────────────────────────────────────────────────────────────┐
│  PREPARE PHASE (Fast: 1-5 minutes)                         │
│                                                              │
│  1. Clone repository                                        │
│  2. Compile project (mvn compile)                           │
│  3. Detect test classes                                     │
│  4. Map tests to production classes                         │
│  5. Compile tests (mvn test-compile)                        │
│                                                              │
│  Output: test-mapping.json                                  │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       │ ← Inspect, modify if needed
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  ANALYZE PHASE (Slow: 10-60 minutes)                       │
│                                                              │
│  1. Instrument classes with Daikon                          │
│  2. Run tests with Chicory (collect traces)                 │
│  3. Generate invariants from traces                         │
│  4. Convert to JML specifications                           │
│  5. Decorate source files with JML                          │
│                                                              │
│  Output: daikon-output/, jml-decorated-classes/             │
└─────────────────────────────────────────────────────────────┘
```

## Detailed Command Reference

### Prepare Command

Clones, compiles, and detects tests in a repository.

**Syntax:**
```bash
docker run [DOCKER_OPTIONS] daikon-jml:latest prepare <github-repo-url>
```

**Arguments:**
- `<github-repo-url>`: Full GitHub repository URL (e.g., `https://github.com/user/repo.git`)

**What It Does:**
1. Clones the repository
2. Runs `mvn clean compile`
3. Detects test classes (JUnit 4/5)
4. Maps tests to production classes
5. Runs `mvn test-compile`

**Outputs:**
- Cloned repository in workspace
- `test-mapping.json`: Test-to-class mapping
- Compiled classes in `target/classes/`
- Compiled tests in `target/test-classes/`

**Example:**
```bash
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/apache/commons-lang.git
```

**Windows:**
```powershell
docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  prepare https://github.com/apache/commons-lang.git
```

### Analyze Command

Runs Daikon analysis on a prepared repository.

**Syntax:**
```bash
docker run [DOCKER_OPTIONS] daikon-jml:latest analyze <repo-name>
```

**Arguments:**
- `<repo-name>`: Name of the repository directory (without .git extension)

**Requirements:**
- Repository must have been prepared first
- `test-mapping.json` must exist in the repository directory

**What It Does:**
1. Instruments classes for Daikon analysis
2. Runs tests with Chicory to collect execution traces
3. Generates invariants from traces
4. Converts invariants to JML format
5. Decorates source files with JML annotations

**Outputs:**
- `daikon-output/`: Trace files (*.dtrace.gz), invariant files (*.inv.gz), JML files (*.jml)
- `jml-decorated-classes/`: Source files with JML annotations
- `instrumented-classes/`: Instrumentation metadata

**Example:**
```bash
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze commons-lang
```

**Windows:**
```powershell
docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  analyze commons-lang
```

### Docker Options

**Volume Mounting (Required for Persistence):**
```bash
-v /host/path:/workspace
```
Maps a directory on your machine to the container's workspace.

**Remove Container After Completion:**
```bash
--rm
```
Automatically removes the container after it finishes (recommended).

**Interactive Mode:**
```bash
-it
```
For debugging and manual execution.

**Memory Limits:**
```bash
--memory="4g" --memory-swap="8g"
```
For large projects that need more resources.

**Environment Variables:**
```bash
-e MAVEN_OPTS="-Xmx4g"
```
Pass custom settings to Maven or Daikon.

## Pipeline Architecture

### Prepare Phase Details

```
[1/4] Clone Repository
      ├── git clone <github-url>
      └── Navigate to repo directory

[2/4] Compile Project
      ├── mvn clean compile
      ├── Validate pom.xml
      ├── Download dependencies
      └── Verify Java 8 compatibility

[3/4] Detect Test Classes
      ├── Scan src/test/java/**/*.java
      ├── Identify JUnit annotations (@Test)
      ├── Check for test naming patterns (*Test, *Tests)
      ├── Parse imports to find tested classes
      ├── Analyze class instantiations
      └── Create test-mapping.json

[4/4] Compile Tests
      ├── mvn test-compile
      └── Validate test dependencies
```

### Analyze Phase Details

```
[1/3] Instrument Classes
      ├── Read test-mapping.json
      ├── Identify classes to instrument
      ├── Configure Chicory
      └── Prepare trace file locations

[2/3] Run Tests with Daikon
      ├── For each test class:
      │   ├── Execute with Chicory instrumentation
      │   ├── Collect runtime traces (*.dtrace.gz)
      │   └── Generate invariants (*.inv.gz)
      ├── Process all trace files
      └── Convert to JML format (*.jml)

[3/3] Decorate Source Files
      ├── For each instrumented class:
      │   ├── Read original source
      │   ├── Find corresponding JML specs
      │   ├── Insert JML as comments
      │   └── Save to jml-decorated-classes/
      └── Preserve original formatting
```

## Output Structure

After running both phases, the repository directory contains:

```
workspace/
└── <repository-name>/
    ├── src/                          # Original source (unchanged)
    │   ├── main/java/
    │   └── test/java/
    │
    ├── target/                       # Maven build output
    │   ├── classes/
    │   └── test-classes/
    │
    ├── test-mapping.json            # Created by PREPARE phase
    │
    ├── daikon-output/               # Created by ANALYZE phase
    │   ├── com_example_Calculator.dtrace.gz      # Execution traces
    │   ├── com_example_Calculator.inv.gz         # Binary invariants
    │   ├── com_example_Calculator.jml            # JML format
    │   └── ...
    │
    ├── instrumented-classes/        # Created by ANALYZE phase
    │   └── classes-to-instrument.txt
    │
    └── jml-decorated-classes/       # Created by ANALYZE phase
        └── com/example/
            ├── Calculator.java       # With JML annotations
            └── MathUtils.java
```

### Key Files Explained

#### test-mapping.json

Maps test classes to the production classes they test:

```json
{
  "com.example.service.UserServiceTest": {
    "test_file": "src/test/java/com/example/service/UserServiceTest.java",
    "tested_classes": [
      "com.example.service.UserService",
      "com.example.model.User"
    ]
  }
}
```

#### *.dtrace.gz

Binary execution trace files containing:
- Program point entries/exits
- Variable values at each point
- Object relationships
- Method call sequences

#### *.inv.gz

Binary invariant files with discovered invariants and confidence levels.

#### *.jml

Human-readable JML specifications:

```java
/*@
  @ requires x >= 0;
  @ requires y >= 0;
  @ ensures \result >= x;
  @ ensures \result >= y;
  @ ensures \result == x + y;
  @*/
```

#### Decorated Java Files

Original source with JML comments:

```java
/*@
 * JML specifications generated by Daikon
 * These represent dynamically detected invariants
 */
/*@
 * Daikon invariants:
 * this.balance >= 0
 * this.accountNumber != null
 * this.accountNumber.length() == 10
 */
public class BankAccount {
    /*@ invariant balance >= 0; */
    private double balance;
    
    /*@ 
      @ requires amount > 0;
      @ ensures balance == \old(balance) + amount;
      @*/
    public void deposit(double amount) {
        balance += amount;
    }
}
```

## Examples

### Example 1: Basic Two-Phase Analysis

```bash
# Create workspace
mkdir -p workspace

# Prepare a simple calculator project
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/example/simple-calculator.git

# Inspect what was found
cat workspace/simple-calculator/test-mapping.json

# Run analysis
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze simple-calculator

# View results
ls workspace/simple-calculator/jml-decorated-classes/
```

### Example 2: Large Project (Apache Commons)

```bash
# Prepare phase
docker run --rm \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/apache/commons-lang.git

# Check test mapping before heavy analysis
cat workspace/commons-lang/test-mapping.json | head -20

# Analyze with more memory
docker run --rm \
  --memory="4g" \
  -e MAVEN_OPTS="-Xmx3g" \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze commons-lang
```

### Example 3: Inspect Before Analysis

```bash
# Prepare
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/user/repo.git

# Inspect compilation
cd workspace/repo
mvn verify

# Check test coverage
mvn jacoco:report
open target/site/jacoco/index.html

# Review test mapping
cat test-mapping.json | jq

# Decide if coverage is sufficient, then analyze
docker run --rm -v $(pwd)/../:/workspace \
  daikon-jml:latest \
  analyze repo
```

### Example 4: Filter Tests Between Phases

```bash
# Prepare
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/user/repo.git

# Edit test-mapping.json to remove slow or irrelevant tests
cd workspace/repo
# Remove unwanted test classes from test-mapping.json
nano test-mapping.json

# Analyze with filtered tests
docker run --rm -v $(pwd)/../:/workspace \
  daikon-jml:latest \
  analyze repo
```

### Example 5: Batch Processing Multiple Projects

```bash
#!/bin/bash
# batch-prepare.sh

REPOS=(
  "https://github.com/user/project1.git"
  "https://github.com/user/project2.git"
  "https://github.com/user/project3.git"
)

# Prepare all projects
for repo in "${REPOS[@]}"; do
  echo "Preparing: $repo"
  docker run --rm -v $(pwd)/workspace:/workspace \
    daikon-jml:latest prepare "$repo"
done

# Analyze them later (can be run in parallel on different machines)
for repo in project1 project2 project3; do
  echo "Analyzing: $repo"
  docker run --rm -v $(pwd)/workspace:/workspace \
    daikon-jml:latest analyze "$repo"
done
```

### Example 6: Resume After Failure

```bash
# If analyze phase fails midway
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze my-repo
# ERROR at step 2/3...

# Just re-run analyze phase (no need to prepare again)
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze my-repo
```

### Example 7: Windows PowerShell Complete Workflow

```powershell
# Create workspace
New-Item -ItemType Directory -Force -Path workspace

# Prepare
docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  prepare https://github.com/facebook/facebook-java-business-sdk.git

# Check results
Get-Content workspace/facebook-java-business-sdk/test-mapping.json | Select-Object -First 20

# Analyze
docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  analyze facebook-java-business-sdk

# View JML files
Get-ChildItem workspace/facebook-java-business-sdk/jml-decorated-classes -Recurse -Filter *.java
```

## Advanced Usage

### Parallel Analysis

```bash
# Prepare multiple projects
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare https://github.com/user/proj1.git
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare https://github.com/user/proj2.git
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare https://github.com/user/proj3.git

# Analyze in parallel (if system has resources)
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze proj1 &
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze proj2 &
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze proj3 &
wait
```

### Interactive Debugging

```bash
# Prepare normally
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/user/repo.git

# Start interactive session for manual analysis
docker run -it --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest bash

# Inside container
cd repo
python3 /usr/local/bin/process_project.py instrument-daikon
python3 /usr/local/bin/process_project.py run-daikon
# Debug specific issues
ls -la daikon-output/
```

### Custom Analysis Script

```bash
#!/bin/bash
# smart-analyze.sh

REPO_URL=$1
REPO_NAME=$(basename "$REPO_URL" .git)

# Phase 1: Prepare
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest prepare "$REPO_URL"

# Check test coverage
cd workspace/$REPO_NAME
mvn jacoco:report 2>&1 | grep "Total.*%"

# Check test mapping
TEST_COUNT=$(jq 'length' test-mapping.json)
echo "Found $TEST_COUNT test classes"

if [ "$TEST_COUNT" -lt 5 ]; then
  echo "Warning: Low number of tests. Results may be limited."
fi

# Phase 2: Analyze
docker run --rm -v $(pwd)/../:/workspace \
  daikon-jml:latest analyze "$REPO_NAME"

# Generate summary
echo "=== Analysis Summary ==="
echo "Invariant files: $(ls daikon-output/*.inv.gz 2>/dev/null | wc -l)"
echo "JML files: $(find jml-decorated-classes -name "*.java" 2>/dev/null | wc -l)"
```

### CI/CD Integration

```yaml
# .github/workflows/daikon-analysis.yml
name: Daikon JML Analysis

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  prepare:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout Daikon Docker
        uses: actions/checkout@v3
        with:
          repository: your-org/daikon-docker
          path: daikon-docker
      
      - name: Build Daikon Image
        run: docker build -t daikon-jml daikon-docker/
      
      - name: Prepare Project
        run: |
          docker run --rm \
            -v ${{ github.workspace }}/results:/workspace \
            daikon-jml:latest \
            prepare https://github.com/${{ github.repository }}.git
      
      - name: Upload Prepared Project
        uses: actions/upload-artifact@v3
        with:
          name: prepared-project
          path: results/
          retention-days: 1

  analyze:
    needs: prepare
    runs-on: ubuntu-latest
    steps:
      - name: Download Prepared Project
        uses: actions/download-artifact@v3
        with:
          name: prepared-project
          path: results/
      
      - name: Checkout Daikon Docker
        uses: actions/checkout@v3
        with:
          repository: your-org/daikon-docker
          path: daikon-docker
      
      - name: Build Daikon Image
        run: docker build -t daikon-jml daikon-docker/
      
      - name: Run Analysis
        run: |
          REPO_NAME=$(basename ${{ github.repository }})
          docker run --rm \
            --memory="4g" \
            -v ${{ github.workspace }}/results:/workspace \
            daikon-jml:latest \
            analyze $REPO_NAME
      
      - name: Upload Analysis Results
        uses: actions/upload-artifact@v3
        with:
          name: daikon-jml-results
          path: |
            results/**/daikon-output/
            results/**/jml-decorated-classes/
            results/**/test-mapping.json
```

## Troubleshooting

### Common Issues and Solutions

#### Issue: "exec /usr/local/bin/entrypoint.sh: no such file or directory"

**Causes:**
- File wasn't copied during Docker build
- Windows line ending issues (CRLF vs LF)
- File not in build context

**Solution:**
```bash
# Check files exist locally
ls -la Dockerfile entrypoint.sh process_project.py

# On Windows: Fix line endings
dos2unix entrypoint.sh  # If you have dos2unix
# OR in PowerShell:
$content = Get-Content entrypoint.sh -Raw
$content = $content -replace "`r`n", "`n"
[System.IO.File]::WriteAllText("entrypoint.sh", $content)

# Rebuild without cache
docker build --no-cache -t daikon-jml:latest .

# Verify file is in image
docker run --rm daikon-jml:latest ls -la /usr/local/bin/
```

#### Issue: "Repository directory not found" (analyze command)

**Cause:** Running analyze before prepare

**Solution:**
```bash
# Always run prepare first
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/user/repo.git

# Then analyze
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze repo
```

#### Issue: "test-mapping.json not found"

**Cause:** Prepare phase didn't complete successfully

**Solution:**
```bash
# Re-run prepare and check for errors
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/user/repo.git 2>&1 | tee prepare.log

# Check the log
cat prepare.log
```

#### Issue: "Maven compilation failed"

**Causes:**
- Missing dependencies
- Java version incompatibility
- Corrupted pom.xml

**Solution:**
```bash
# Test compilation locally first
git clone https://github.com/user/repo.git
cd repo
mvn clean compile

# If it works locally, try prepare again
docker run --rm -v $(pwd)/../workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/user/repo.git
```

#### Issue: "No test classes detected"

**Causes:**
- Tests in non-standard location
- Missing JUnit annotations
- Test dependencies not in pom.xml

**Solution:**
```bash
# Check test structure
ls -R src/test/java/

# Verify JUnit in pom.xml
grep -A5 "junit" pom.xml

# Check if tests have @Test annotations
grep -r "@Test" src/test/java/
```

#### Issue: "Out of memory error" during analyze

**Solution:**
```bash
# Increase Docker memory
docker run --rm \
  --memory="4g" \
  --memory-swap="8g" \
  -e MAVEN_OPTS="-Xmx3g" \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze repo
```

#### Issue: Analyze phase takes too long

**Solution:**
```bash
# Filter tests before analysis
cd workspace/repo
# Edit test-mapping.json to remove slow tests
nano test-mapping.json

# Or run on specific test classes only
# Manually edit test-mapping.json to keep only fast tests
```

#### Issue: Volume not persisting (Windows)

**Cause:** Incorrect path format

**Solution:**
```powershell
# Use ${PWD} in PowerShell
docker run --rm -v ${PWD}/workspace:/workspace ...

# Or use absolute path with forward slashes
docker run --rm -v C:/Users/YourName/workspace:/workspace ...

# NOT backslashes
```

### Debug Mode

For detailed troubleshooting:

```bash
# Run interactively
docker run -it --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest bash

# Inside container, run commands manually
cd /workspace
/usr/local/bin/entrypoint.sh prepare https://github.com/user/repo.git
# Or
cd repo-name
python3 /usr/local/bin/process_project.py detect-tests
```

## Technical Details

### Technologies Used

| Component | Version | Purpose |
|-----------|---------|---------|
| Ubuntu | 22.04 | Base OS |
| OpenJDK | 8 | Java runtime |
| Maven | Latest | Build tool |
| Daikon | 5.8.18 | Invariant detection |
| Python | 3.x | Scripting |
| Git | Latest | VCS |

### Daikon Components

- **Chicory**: Instruments Java bytecode to collect traces
- **DynComp**: Analyzes dynamic comparability
- **Daikon**: Core invariant detector
- **PrintInvariants**: Formats output to various specifications (Java, JML, ESC/Java, DBC)

### Performance Characteristics

| Project Size | Prepare Time | Analyze Time | Memory Usage |
|--------------|--------------|--------------|--------------|
| Small (< 50 classes, < 100 tests) | 1-2 min | 5-10 min | 512MB - 1GB |
| Medium (50-200 classes, 100-500 tests) | 2-5 min | 15-30 min | 1GB - 2GB |
| Large (200-500 classes, 500-2000 tests) | 5-10 min | 30-60 min | 2GB - 4GB |
| Very Large (500+ classes, 2000+ tests) | 10-20 min | 1-3 hours | 4GB+ |

**Note:** Analyze phase is significantly slower than prepare phase due to:
- Runtime instrumentation overhead
- Test execution time
- Trace file I/O
- Invariant inference computation

### Invariant Types Detected

Daikon can detect 100+ types of invariants including:

**Unary invariants** (single variable):
- `x == c` (constant value)
- `x > c` (range)
- `x != null` (non-null)
- `x in {1, 2, 3}` (set membership)

**Binary invariants** (two variables):
- `x < y` (ordering)
- `x == y` (equality)
- `x == y + c` (linear relationship)
- `array[i] == value` (array element)

**Ternary invariants** (three variables):
- `x == y + z` (linear combination)

**Sequence invariants**:
- `array.length > 0` (non-empty)
- `array is sorted`
- `array has no duplicates`

**Object invariants**:
- `obj.field != null`
- `obj1.id == obj2.id`
- `collection.size() == count`

## Limitations

### Current Limitations

1. **Two-phase approach requires volume persistence**
   - Must use `-v` flag to persist data between phases
   - Cannot run analyze without running prepare first

2. **Public repositories by default**
   - Private repos require authentication setup
   - Workaround: Use personal access tokens or SSH keys

3. **Maven projects only**
   - Gradle projects not supported
   - Ant projects not supported

4. **Java 8 specific**
   - Newer Java versions may have compatibility issues
   - Workaround: Use Java 8 compatible syntax

5. **JUnit 4/5 only**
   - TestNG not supported
   - Custom test frameworks not supported
   - Workaround: Convert tests to JUnit

6. **Standard Maven layout required**
   - Non-standard directory structures may fail
   - Workaround: Restructure project or modify detection script

7. **Test execution requirements**
   - Tests must run without external dependencies
   - No database, API, or file system dependencies during test execution
   - Workaround: Use mocks, test containers, or embedded databases

8. **Memory constraints**
   - Very large projects may exceed memory
   - Workaround: Increase Docker memory allocation or filter tests

9. **Processing time**
   - Large codebases can take hours
   - No incremental analysis (must re-run entire analyze phase)
   - Workaround: Run overnight or filter to specific modules

10. **Two-phase requires same workspace**
    - Both phases must access the same volume mount
    - Cannot easily split phases across different machines without copying data

### Known Issues

- **Unicode handling**: Some non-ASCII characters in source files may cause issues
- **Complex generics**: Deep generic type hierarchies may not be fully analyzed
- **Dynamic class loading**: Reflectively loaded classes won't be instrumented
- **Native methods**: JNI methods cannot be analyzed
- **Test dependencies**: Tests that depend on each other may produce incomplete results
- **Flaky tests**: Non-deterministic tests may produce inconsistent invariants

## FAQ

### General Questions

**Q: Why split into two phases?**  
A: The two-phase approach allows you to:
- Verify compilation quickly before running intensive analysis
- Inspect and modify test selection between phases
- Resume analysis if it fails without re-cloning and re-compiling
- Batch prepare multiple projects and analyze them later

**Q: Can I run both phases in one command?**  
A: Not directly, but you can create a wrapper script:
```bash
#!/bin/bash
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare $1
REPO_NAME=$(basename $1 .git)
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze $REPO_NAME
```

**Q: How long does each phase take?**  
A: 
- **Prepare**: 1-10 minutes (depending on project size and compilation complexity)
- **Analyze**: 10-60+ minutes (depending on number of tests and code complexity)

**Q: Is my code sent anywhere?**  
A: No, all processing happens locally in the Docker container. Nothing is uploaded.

**Q: What happens to my repository after analysis?**  
A: The cloned repository and results remain in your workspace directory. Nothing is modified on GitHub.

### Technical Questions

**Q: Can I run analyze multiple times on the same prepared project?**  
A: Yes! You can re-run the analyze phase as many times as you want:
```bash
# Prepare once
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>

# Analyze multiple times (maybe with different settings)
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze <repo>
docker run --rm --memory="8g" -v $(pwd)/workspace:/workspace daikon-jml:latest analyze <repo>
```

**Q: Can I modify test-mapping.json between phases?**  
A: Yes! This is one of the key benefits of the two-phase approach:
```bash
# Prepare
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>

# Edit test-mapping.json to remove unwanted tests
nano workspace/repo/test-mapping.json

# Analyze with filtered tests
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo
```

**Q: Why Java 8 specifically?**  
A: Daikon 5.8.18 is tested and optimized for Java 8. Newer versions may work but aren't guaranteed to be compatible.

**Q: Can I use this in CI/CD?**  
A: Yes! See the CI/CD integration example in the Advanced Usage section.

**Q: How accurate are the invariants?**  
A: Accuracy depends on test coverage. With good tests (>70% coverage), invariants are typically very accurate. However, they represent what the tests exercise, not all possible program behaviors.

**Q: Can I use the generated JML for formal verification?**  
A: Yes! The JML output is compatible with tools like OpenJML and ESC/Java2. However, you may need to manually refine some specifications.

**Q: Does this modify my source code?**  
A: No, original source is unchanged. Decorated files are saved separately in `jml-decorated-classes/`.

**Q: Can I analyze only specific packages or classes?**  
A: Yes, edit `test-mapping.json` after the prepare phase to include only the tests/classes you want to analyze.

**Q: What if my tests fail during the analyze phase?**  
A: Daikon will still try to process the traces it collected before the failure. You may get partial results.

**Q: Can I run prepare and analyze on different machines?**  
A: Yes, but you need to copy the entire workspace directory between machines:
```bash
# On machine 1
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>
tar czf workspace.tar.gz workspace/

# Transfer workspace.tar.gz to machine 2
# On machine 2
tar xzf workspace.tar.gz
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze <repo>
```

**Q: How do I increase memory for large projects?**  
A: Use Docker's `--memory` flag and set `MAVEN_OPTS`:
```bash
docker run --rm \
  --memory="8g" \
  --memory-swap="16g" \
  -e MAVEN_OPTS="-Xmx6g" \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest analyze <repo>
```

**Q: Can I run multiple analyze phases in parallel?**  
A: Yes, if they're analyzing different repositories:
```bash
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo1 &
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo2 &
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo3 &
wait
```

**Q: What if prepare succeeds but analyze fails?**  
A: You can debug and re-run just the analyze phase:
```bash
# Check what went wrong
docker run -it --rm -v $(pwd)/workspace:/workspace daikon-jml:latest bash
cd <repo>
cat daikon-output/*.log

# Fix issues (e.g., increase memory, filter tests)
# Re-run analyze
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze <repo>
```

### Workflow Questions

**Q: Should I always run prepare before analyze?**  
A: Yes, analyze requires the outputs from prepare (compiled classes, test-mapping.json).

**Q: Can I skip the prepare phase if I already have the repository?**  
A: No, prepare does more than just cloning. It compiles the project and creates the test mapping. However, if you run prepare again on an existing repository, it will reuse it and just pull updates.

**Q: What's the best workflow for development?**  
A: 
1. Run prepare once on your project
2. Develop and modify code
3. Re-run prepare if you add new tests or classes
4. Run analyze whenever you want to update JML specifications
5. Review JML output and integrate into your documentation

**Q: Can I automate this in a nightly build?**  
A: Yes! Use the CI/CD example or create a cron job:
```bash
#!/bin/bash
# nightly-daikon.sh
cd /path/to/workspace
docker run --rm -v $(pwd):/workspace daikon-jml:latest prepare https://github.com/myorg/myrepo.git
docker run --rm -v $(pwd):/workspace daikon-jml:latest analyze myrepo
# Email or upload results
```

Add to crontab:
```
0 2 * * * /path/to/nightly-daikon.sh
```

## Platform-Specific Notes

### Linux

Standard commands work as documented:
```bash
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze <repo>
```

### macOS

Same as Linux, but be aware:
- Docker Desktop may need increased memory allocation (Preferences → Resources → Memory)
- File system performance may be slower with volume mounts
- Use Docker Desktop's built-in terminal or iTerm2

### Windows

**PowerShell (Recommended):**
```powershell
docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  prepare https://github.com/user/repo.git

docker run --rm -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  analyze repo
```

**Command Prompt:**
```cmd
docker run --rm -v %cd%\workspace:/workspace daikon-jml:latest prepare https://github.com/user/repo.git
docker run --rm -v %cd%\workspace:/workspace daikon-jml:latest analyze repo
```

**Git Bash:**
```bash
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo
```

**Common Windows Issues:**
- Line ending problems: Convert `entrypoint.sh` to Unix format (LF)
- Path format: Use forward slashes `/` in volume mounts
- WSL2: Make sure Docker is using WSL2 backend for better performance

## Best Practices

### 1. Always Use Volume Mounts

```bash
# ✓ Good - results persist
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>

# ✗ Bad - results lost after container stops
docker run --rm daikon-jml:latest prepare <url>
```

### 2. Check Test Coverage Before Analysis

```bash
# After prepare, check coverage
cd workspace/repo
mvn jacoco:report
# Review target/site/jacoco/index.html

# Only proceed with analyze if coverage is good
```

### 3. Start Small

```bash
# Test with a small project first
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/user/simple-calculator.git

# Once comfortable, move to larger projects
```

### 4. Inspect Test Mapping

```bash
# After prepare, review what will be analyzed
cat workspace/repo/test-mapping.json | jq

# Remove tests that:
# - Take too long
# - Test external integrations
# - Are flaky
```

### 5. Monitor Resources

```bash
# During analyze phase, monitor in another terminal
docker stats

# If memory usage is high, increase allocation
docker run --rm --memory="8g" -v $(pwd)/workspace:/workspace \
  daikon-jml:latest analyze repo
```

### 6. Keep Workspace Organized

```bash
workspace/
├── project1/
├── project2/
└── project3/

# Not:
workspace/
├── project1/
├── project1-copy/
├── project1-old/  # Don't keep multiple versions
```

### 7. Use Absolute Paths in Scripts

```bash
# ✓ Good
WORKSPACE_DIR=$(pwd)/workspace
docker run --rm -v $WORKSPACE_DIR:/workspace daikon-jml:latest prepare <url>

# ✗ Bad - may break if script runs from different directory
docker run --rm -v ./workspace:/workspace daikon-jml:latest prepare <url>
```

### 8. Document Your Workflow

Create a `README.md` in your workspace:
```markdown
# Daikon Analysis Workspace

## Last Updated
2025-10-23

## Projects Analyzed
- project1: Prepared on 2025-10-20, Analyzed on 2025-10-21
- project2: Prepared on 2025-10-22, Analyzed on 2025-10-23

## Commands Used
Prepare: docker run --rm -v $(pwd):/workspace daikon-jml:latest prepare <url>
Analyze: docker run --rm --memory="4g" -v $(pwd):/workspace daikon-jml:latest analyze <repo>
```

## Contributing

Contributions are welcome! Here are ways to help:

### Reporting Issues

When reporting issues, please include:
- Docker version (`docker --version`)
- Operating system
- Complete command used
- Error output
- Repository URL (if public)
- `test-mapping.json` content (if relevant)

### Improving Detection

Help improve test detection by:
- Testing with diverse project structures
- Reporting false positives/negatives
- Contributing regex patterns for edge cases

### Documentation

- Fix typos or unclear sections
- Add more examples
- Translate to other languages
- Create video tutorials

### Code Improvements

- Optimize performance
- Add support for Gradle
- Improve JML formatting
- Add more output formats

## License

This Docker configuration is provided as-is for educational and research purposes.

### Component Licenses

- **Daikon**: MIT License - https://plse.cs.washington.edu/daikon/
- **Maven**: Apache License 2.0 - https://maven.apache.org/
- **JUnit**: Eclipse Public License - https://junit.org/
- **Ubuntu**: Various open-source licenses
- **OpenJDK**: GPL v2 with Classpath Exception

## References

- [Daikon Invariant Detector](https://plse.cs.washington.edu/daikon/) - Official Daikon website
- [Daikon User Manual](https://plse.cs.washington.edu/daikon/download/doc/daikon.html) - Complete documentation
- [JML (Java Modeling Language)](https://www.openjml.org/) - JML specification
- [OpenJML](https://www.openjml.org/) - JML verification tool
- [Maven Documentation](https://maven.apache.org/guides/) - Maven guides
- [JUnit 5 Documentation](https://junit.org/junit5/docs/current/user-guide/) - JUnit 5 guide
- [Docker Documentation](https://docs.docker.com/) - Docker reference

## Citation

If you use this tool in academic research, please cite:

```bibtex
@misc{daikon-jml-docker,
  title={JavaISA: Daikon JML Instrumentation Docker Tool},
  author={Juan Carlos Recio Abad},
  year={2025},
  howpublished={\url{https://github.com/jcrecio/JavaISA}}
}
```

And cite the original Daikon paper:

```bibtex
@inproceedings{Ernst2007,
  author = {Ernst, Michael D. and Perkins, Jeff H. and Guo, Philip J. and McCamant, Stephen and Pacheco, Carlos and Tschantz, Matthew S. and Xiao, Chen},
  title = {The Daikon System for Dynamic Detection of Likely Invariants},
  booktitle = {Science of Computer Programming},
  year = {2007},
  volume = {69},
  number = {1-3},
  pages = {35--45}
}
```

## Acknowledgments

- Daikon development team at MIT and University of Washington
- JML community
- Apache Maven project
- JUnit team
- Docker community

## Support

For issues and questions:

1. **Check this README** for common solutions
2. **Review Troubleshooting section** for known issues
3. **Search Daikon documentation** for Daikon-specific questions
4. **Open an issue** on GitHub with detailed information
5. **Community forums** for general Docker/Maven/Java questions

## Changelog

### Version 2.0.0 (2025-10-23)
- **BREAKING**: Split workflow into two phases (prepare and analyze)
- Added ability to inspect and modify test mapping between phases
- Improved error handling and reporting
- Added support for resuming failed analysis
- Enhanced documentation with two-phase examples

### Version 1.0.0 (Initial Release)
- Single-phase pipeline
- Automatic test detection
- JML generation
- Basic Docker setup

## Roadmap

Future enhancements planned:

- [ ] Support for Gradle projects
- [ ] Incremental analysis (only analyze changed classes)
- [ ] Web UI for viewing results
- [ ] Integration with IDE plugins
- [ ] Support for Java 11+ projects
- [ ] Parallel test execution
- [ ] Custom invariant filters
- [ ] Export to additional formats (Alloy, Z3, etc.)
- [ ] Docker Compose for multi-container setup
- [ ] Pre-built Docker images on Docker Hub

---

**Last Updated**: October 23, 2025 
**Version**: 2.0.0  
**Maintainer**: Juan Carlos Recio Abad <jcrecio@uma.es>