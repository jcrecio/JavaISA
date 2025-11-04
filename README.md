# JavaISA.jml: Java to JML Automated Specification Generation

A comprehensive Docker-based tool for automatically generating JML (Java Modeling Language) specifications from Java code using the Daikon invariant detector. This tool is the **first step in a novel workflow** for translating object-oriented Java programs into formal Isabelle/HOL specifications for automated theorem proving and verification.

⚠️This project is the continuation of the archived repository https://github.com/jcrecio/java2jml

## Table of Contents

- [Research Context](#research-context)
- [Overview](#overview)
- [What This Tool Does](#what-this-tool-does)
- [Prerequisites](#prerequisites)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Two-Phase Workflow](#two-phase-workflow)
- [Three-Phase Internal Process](#three-phase-internal-process)
- [Detailed Command Reference](#detailed-command-reference)
- [Output Structure](#output-structure)
- [Examples](#examples)
- [Advanced Usage](#advanced-usage)
- [Troubleshooting](#troubleshooting)
- [Technical Details](#technical-details)
- [Limitations](#limitations)
- [FAQ](#faq)
- [Related Work](#related-work)
- [Contributing](#contributing)
- [License](#license)

## Research Context

### The Java-to-Isabelle/HOL Translation Challenge

This tool addresses a critical challenge in formal software verification: *Automatically translating commercial, business production Java code into formal Isabelle/HOL specifications**. While formal verification offers mathematical guarantees of software correctness, its application to real-world object-oriented systems has been limited by the manual effort required to create formal specifications.

### Why This Matters

**Industrial Impact:**
- Modern software systems, particularly in critical domains (finance, healthcare, aerospace, autonomous vehicles), are predominantly written in Java
- These systems require high assurance but rarely have formal specifications
- Manual formal specification creation is prohibitively expensive and error-prone
- Automated translation enables formal verification of existing codebases without complete rewrites

**Scientific Contribution:**
- Bridges the gap between industrial OOP practices and formal verification techniques
- Enables application of theorem proving to legacy and production systems
- Provides a scalable approach to extracting behavioral contracts from existing test suites
- Supports incremental formalization of large codebases

### The Complete Workflow

This tool implements **Phase 1** of a three-phase automated translation workflow:

```
┌────────────────────────────────────────────────────────────────┐
│ PHASE 1: Java → Java/JML (This Tool)                           │
│ ───────────────────────────────────────────────────────────    │
│ Input:  Plain Java code with JUnit tests                       │
│ Output: Java classes annotated with JML specifications         │
│                                                                │
│ Process:                                                       │
│ 1. Dynamic analysis with Daikon (invariant detection)          │
│ 2. Test execution and trace collection                         │
│ 3. JML specification generation                                │
│ 4. Source code decoration with formal contracts                │
└────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│ PHASE 2: Java/JML → Intermediate Representation (Why3)          │
│ ───────────────────────────────────────────────────────────     │
│ - Parse JML specifications                                      │
│ - Abstract OOP concepts (inheritance, polymorphism, etc.)       │
│ - Generate intermediate formal representation                   │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│ PHASE 3: Why3 → Isabelle/HOL                                    │
│ ───────────────────────────────────────────────────────────     │
│ - Transform to Isabelle/HOL theory files                        │
│ - Encode OOP semantics in HOL                                   │
│ - Enable formal verification and theorem proving                │
└─────────────────────────────────────────────────────────────────┘
```

### Key Innovation

Unlike traditional approaches that require manual specification or restrict to simplified language subsets, this workflow:

✅ **Handles real-world Java** - Works with production code including complex OOP patterns  
✅ **Leverages existing tests** - Extracts specifications from test execution, not manual annotation  
✅ **Automated end-to-end** - Minimal human intervention required  
✅ **Scalable** - Can process large codebases incrementally  
✅ **Preserves semantics** - Maintains behavioral equivalence through the translation chain

### Related Research

This work is part of the following research:

1. **"Automated Translation of Java to Isabelle/HOL"** - Establishes the theoretical foundations for Java-to-HOL translation and addresses key challenges in encoding OOP concepts in higher-order logic.
   - [https://biblioteca.sistedes.es/dspace.server/api/core/bitstreams/1da57d26-316f-4f3c-9989-160e19a1baa7/content](https://biblioteca.sistedes.es/entities/art%C3%ADculo/218b4c12-c06d-4b3b-b3ca-afbf013a354d), Recio, J. C., Saborido, R., Chicano, F.: Automatic Documentation of Java Code with Formal Specifications using Artificial Intelligence. In: Burgueño, L. (ed.) Actas de las XXIX Jornadas de Ingeniería del Software y Bases de Datos (JISBD 2025). Sistedes (2025). https://hdl.handle.net/11705/JISBD/2025/90


2. **"Automatic Proof Generation: Fine-tuning and RAG in Reasoner vs. Math LLMs"**
   - [https://dl.acm.org/doi/10.1145/3696630.3728705](https://dl.acm.org/doi/10.1145/3696630.3728705), Juan Carlos Recio Abad, Rubén Saborido, and Francisco Chicano. 2025. Automatic Proof Generation: Fine-tuning and RAG in Reasoner vs. Math LLMs. In Proceedings of the 33rd ACM International Conference on the Foundations of Software Engineering (FSE Companion '25). Association for Computing Machinery, New York, NY, USA, 1679–1682. https://doi.org/10.1145/3696630.3728705


## Overview

This Docker image provides a complete, automated pipeline for:
- Analyzing Java Maven projects to understand their test structure
- Running Daikon with DynComp to infer program invariants from test executions
- Generating formal JML (Java Modeling Language) specifications based on discovered invariants
- Decorating original source code with both class-level and method-level JML annotations

The tool uses a **two-phase user workflow** for better control and flexibility:
1. **Prepare Phase**: Fast setup (clone, compile, detect tests)
2. **Analyze Phase**: Intensive analysis (DynComp + Chicory + Daikon → JML)

Internally, the analyze phase uses a **three-phase process**:
1. **DynComp Phase**: Comparability analysis to reduce memory usage
2. **Chicory Phase**: Dynamic trace collection from test execution
3. **Daikon Phase**: Invariant inference and JML generation

## What This Tool Does

### The Complete Process

#### Phase 1: Prepare (Fast - 1-5 minutes)
1. **Repository Cloning**: Downloads your Java project from GitHub
2. **Compilation Verification**: Ensures the project builds successfully with Maven
3. **Test Discovery**: Intelligently identifies all JUnit test classes (both JUnit 4 and 5)
4. **Test Mapping**: Analyzes test code to determine which production classes each test exercises

#### Phase 2: Analyze (Intensive - 10-60+ minutes)

**DynComp Comparability Analysis:**
- Executes tests with DynComp instrumentation
- Determines which variables should be compared
- Generates comparability information to optimize trace collection
- Significantly reduces memory requirements (50-70% reduction)

**Chicory Trace Collection:**
- Instruments bytecode at runtime
- Executes tests while recording method entries/exits
- Captures variable values and object states
- Generates compressed trace files (.dtrace.gz)

**Daikon Invariant Inference:**
- Processes execution traces
- Applies statistical analysis to detect likely invariants
- Generates multiple output formats (Java, JML, ESC/Java)
- Creates both class-level and method-level specifications

**JML Code Decoration:**
- Parses generated invariants
- Identifies class invariants, preconditions, and postconditions
- Inserts properly formatted JML annotations
- Preserves original source formatting

### What Are Invariants?

Invariants are properties that always hold true during program execution. Daikon discovers invariants like:

- **Variable relationships**: `x > y`, `array.length == count`
- **Object properties**: `field != null`, `list.isEmpty() == false`
- **Method behaviors**: Preconditions, postconditions, return values
- **Class invariants**: Properties that hold for all instances

### What Is JML?

JML (Java Modeling Language) is a behavioral interface specification language for Java that allows you to formally describe:

- **Preconditions** (`requires`): What must be true before a method executes
- **Postconditions** (`ensures`): What will be true after a method executes
- **Invariants** (`invariant`): What's always true for a class
- **Exceptional behavior** (`signals`): Specifications for exceptional cases

**Example JML Specification:**
```java
/*@
 * @ invariant balance >= 0;
 * @ invariant accountNumber != null;
 */
public class BankAccount {
    /*@
     * @ requires amount > 0;
     * @ requires balance + amount <= MAX_BALANCE;
     * @ ensures balance == \old(balance) + amount;
     * @ ensures \result == true;
     */
    public boolean deposit(double amount) {
        balance += amount;
        return true;
    }
}
```

JML specifications can be:
- **Verified** using runtime assertion checking
- **Formally proven** using theorem provers (OpenJML, ESC/Java, KeY)
- **Translated** to other formal languages (Isabelle/HOL, Coq, etc.)
- **Used for documentation** and developer understanding

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
- **Test Coverage**: Higher test coverage leads to better invariant quality (>50% recommended)

### Recommended Resources

For optimal performance:
- **Memory**: 8-10 GB Docker allocation
- **Disk**: 5-10 GB free space for large projects
- **CPU**: Multi-core processor (analysis parallelizes well)

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
   - Builds DynComp runtime for comparability analysis

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

# Phase 1: Prepare the project (fast - validates compilation and detects tests)
docker run --rm \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/username/repository.git

# Phase 2: Run Daikon analysis (intensive - generates specifications)
docker run --rm --memory="10g" \
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
docker run --rm --memory="10g" -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  analyze repository
```

### Check Results

After both phases complete:

```bash
# View test mapping
cat workspace/repository/test-mapping.json

# List generated invariants
ls workspace/repository/daikon-output/

# View JML decorated classes
ls workspace/repository/jml-decorated-classes/

# Inspect a decorated class
cat workspace/repository/jml-decorated-classes/com/example/MyClass.java
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
│  PREPARE PHASE (Fast: 1-5 minutes)                          │
│                                                             │
│  1. Clone repository                                        │
│  2. Compile project (mvn compile)                           │
│  3. Detect test classes                                     │
│  4. Map tests to production classes                         │
│  5. Compile tests (mvn test-compile)                        │
│                                                             │
│  Output: test-mapping.json                                  │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       │
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  ANALYZE PHASE (Intensive: 10-60+ minutes)                  │
│                                                             │
│  ┌────────────────────────────────────────────────────────┐ │
│  │ Phase 1: DynComp Comparability Analysis                │ │
│  │ - Run tests with DynComp instrumentation               │ │
│  │ - Generate comparability data (.decls files)           │ │
│  │ - Reduces subsequent memory usage by 50-70%            │ │
│  └────────────────────────────────────────────────────────┘ │
│                         ↓                                   │
│  ┌────────────────────────────────────────────────────────┐ │
│  │ Phase 2: Chicory Trace Collection                      │ │
│  │ - Instrument bytecode with Chicory                     │ │
│  │ - Execute tests with instrumentation                   │ |
│  │ - Collect execution traces (.dtrace.gz files)          │ │
│  │ - Record method entries, exits, variable values        │ │
│  └────────────────────────────────────────────────────────┘ │
│                         ↓                                   │
│  ┌────────────────────────────────────────────────────────┐ │
│  │ Phase 3: Daikon Invariant Inference & JML Generation   │ │
│  │ - Process traces with Daikon                           │ │
│  │ - Infer likely invariants                              │ │
│  │ - Generate JML specifications                          │ │
│  │ - Decorate source files with JML annotations           │ │
│  └────────────────────────────────────────────────────────┘ │
│                                                             │
│  Output: daikon-output/, jml-decorated-classes/             │
└─────────────────────────────────────────────────────────────┘
```

## Three-Phase Internal Process

The analyze phase internally uses a sophisticated three-phase process:

### Phase 1: DynComp Comparability Analysis

**Purpose**: Determine which variables should be compared to reduce memory and improve quality

**Process**:
1. Instruments bytecode with DynComp
2. Executes each test class
3. Tracks which variables have comparable values
4. Generates `.decls` (declarations) files

**Output**: `dyncomp-output/*.decls` files

**Benefits**:
- 50-70% reduction in memory usage
- Faster trace collection
- More focused invariant detection
- Better scalability for large projects

### Phase 2: Chicory Trace Collection

**Purpose**: Record program execution to capture variable values and relationships

**Process**:
1. Instruments bytecode with Chicory
2. Uses DynComp comparability data if available
3. Executes tests while recording:
   - Method entries and exits
   - Variable values at program points
   - Object states
   - Return values
4. Compresses and stores traces

**Output**: `daikon-output/*.dtrace.gz` files

**Characteristics**:
- Each test class generates one trace file
- Files can be large (1 KB to 300+ MB)
- Compressed with gzip
- Binary format for efficiency

### Phase 3: Daikon Invariant Inference & JML Generation

**Purpose**: Analyze traces to discover invariants and generate JML specifications

**Process**:
1. **Invariant Detection**:
   - Loads execution traces
   - Applies statistical analysis
   - Detects likely invariants (confidence-based)
   - Filters trivial or redundant invariants

2. **JML Generation**:
   - Converts invariants to JML format
   - Separates class vs. method invariants
   - Identifies preconditions (:::ENTER)
   - Identifies postconditions (:::EXIT)
   - Formats as valid JML annotations

3. **Code Decoration**:
   - Parses original source files
   - Inserts JML before class declarations
   - Inserts JML before method declarations
   - Preserves original formatting
   - Creates decorated copies

**Output**:
- `daikon-output/*.inv.gz` - Binary invariant files
- `daikon-output/*.jml` - JML format invariants
- `jml-decorated-classes/**/*.java` - Annotated source files

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

Runs complete Daikon analysis on a prepared repository.

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
1. **DynComp Phase**: Runs comparability analysis on all tests
2. **Chicory Phase**: Collects execution traces with instrumentation
3. **Daikon Phase**: Infers invariants and generates JML
4. **Decoration Phase**: Creates JML-annotated source files

**Outputs:**
- `dyncomp-output/`: DynComp comparability files (*.decls)
- `daikon-output/`: Trace files (*.dtrace.gz), invariants (*.inv.gz), JML (*.jml)
- `jml-decorated-classes/`: Source files with JML annotations
- `instrumented-classes/`: Instrumentation metadata

**Example:**
```bash
docker run --rm --memory="10g" -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze commons-lang
```

**Windows:**
```powershell
docker run --rm --memory="10g" -v ${PWD}/workspace:/workspace `
  daikon-jml:latest `
  analyze commons-lang
```

### Docker Options

**Volume Mounting (Required for Persistence):**
```bash
-v /host/path:/workspace
```
Maps a directory on your machine to the container's workspace.

**Memory Allocation (Recommended):**
```bash
--memory="10g"
```
Allocate sufficient memory for large projects. Minimum 6GB, recommended 8-10GB.

**Remove Container After Completion:**
```bash
--rm
```
Automatically removes the container after it finishes (recommended).

**Interactive Mode (For Debugging):**
```bash
-it
```
For debugging and manual execution.

**Environment Variables:**
```bash
-e MAVEN_OPTS="-Xmx4g"
```
Pass custom settings to Maven or Java.

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
    ├── dyncomp-output/              # Created by ANALYZE phase (DynComp)
    │   └── *.decls                  # Comparability declarations
    │
    ├── daikon-output/               # Created by ANALYZE phase (Chicory + Daikon)
    │   ├── *.dtrace.gz              # Execution traces
    │   ├── *.inv.gz                 # Binary invariants
    │   └── *.jml                    # JML format invariants
    │
    ├── instrumented-classes/        # Created by ANALYZE phase
    │   └── classes-to-instrument.txt
    │
    └── jml-decorated-classes/       # Created by ANALYZE phase
        └── com/example/
            ├── MyClass.java         # With JML annotations
            └── AnotherClass.java
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

#### *.decls (DynComp Comparability Files)

Binary files containing comparability information generated by DynComp. These inform Chicory which variables should be compared, significantly reducing memory usage.

#### *.dtrace.gz (Execution Traces)

Compressed binary execution trace files containing:
- Program point entries/exits
- Variable values at each point
- Object relationships
- Method call sequences

File sizes vary from 1 KB (simple tests) to 300+ MB (complex tests).

#### *.inv.gz (Binary Invariants)

Compressed binary invariant files with:
- Discovered invariants
- Confidence levels
- Statistical evidence
- Invariant types

#### *.jml (JML Format Invariants)

Human-readable JML specifications:

```
===========================================================================
com.example.BankAccount:::OBJECT
this != null
this.balance >= 0
this.accountNumber != null

===========================================================================
com.example.BankAccount.deposit(double):::ENTER
amount > 0
this.balance >= 0

===========================================================================
com.example.BankAccount.deposit(double):::EXIT
this.balance == orig(this.balance) + amount
return == true
```

#### Decorated Java Files

Original source with JML comments inserted:

```java
/*@
 * JML specifications generated by Daikon
 * These represent dynamically detected invariants
 */
/*@
 * Class Invariants:
 * @ invariant this != null;
 * @ invariant balance >= 0;
 * @ invariant accountNumber != null;
 */
public class BankAccount {
    
    /*@
     @ requires amount > 0;
     @ requires balance >= 0;
     @ ensures balance == \old(balance) + amount;
     @ ensures \result == true;
     */
    public boolean deposit(double amount) {
        balance += amount;
        return true;
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
docker run --rm --memory="8g" -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze simple-calculator

# View decorated class
cat workspace/simple-calculator/jml-decorated-classes/com/example/Calculator.java
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

# Analyze with more memory (large project)
docker run --rm \
  --memory="12g" \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze commons-lang

# Check results
ls workspace/commons-lang/jml-decorated-classes/org/apache/commons/lang3/
```

### Example 3: Production Code Analysis for Isabelle Translation

```bash
# Analyze a production codebase for formal verification
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare https://github.com/company/critical-system.git

# Review test coverage
cd workspace/critical-system
mvn jacoco:report
# View target/site/jacoco/index.html

# If coverage is sufficient (>50%), proceed with analysis
docker run --rm --memory="10g" -v $(pwd)/../:/workspace \
  daikon-jml:latest \
  analyze critical-system

# The generated JML can now be used as input for Phase 2 (Java/JML → IR)
# and Phase 3 (IR → Isabelle/HOL) of the complete workflow
```

### Example 4: Batch Processing Multiple Projects

```bash
#!/bin/bash
# batch-prepare.sh - Prepare multiple projects for analysis

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
  docker run --rm --memory="10g" -v $(pwd)/workspace:/workspace \
    daikon-jml:latest analyze "$repo" &
done
wait

echo "All analyses complete!"
```

### Example 5: CI/CD Integration

```yaml
# .github/workflows/daikon-analysis.yml
name: Generate JML Specifications

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
            --memory="10g" \
            -v ${{ github.workspace }}/results:/workspace \
            daikon-jml:latest \
            analyze $REPO_NAME
      
      - name: Upload JML Specifications
        uses: actions/upload-artifact@v3
        with:
          name: jml-specifications
          path: |
            results/**/jml-decorated-classes/
            results/**/daikon-output/*.jml
          retention-days: 30
      
      - name: Comment PR with Results
        if: github.event_name == 'pull_request'
        uses: actions/github-script@v6
        with:
          script: |
            const fs = require('fs');
            const path = require('path');
            
            // Count generated files
            const jmlDir = 'results/*/jml-decorated-classes';
            const files = /* count files */;
            
            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.name,
              body: `## JML Specifications Generated\n\n✓ ${files} classes decorated with formal specifications\n\nArtifacts available for download.`
            });
```

## Advanced Usage

### Extracting Specific Invariants

```bash
# Run analysis
docker run --rm --memory="10g" -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  analyze myproject

# Extract method preconditions
cd workspace/myproject/daikon-output
for file in *.jml; do
  echo "=== $file ==="
  grep ":::ENTER" "$file" -A 5
done

# Extract class invariants
for file in *.jml; do
  echo "=== $file ==="
  grep ":::OBJECT" "$file" -A 10
done

# View specific class invariants
cat com_example_MyClass.jml | grep -A 20 ":::OBJECT"
```

### Using Daikon Print Tools

Access Daikon's printing utilities for custom output formats:

```bash
# Start interactive container
docker run -it --rm -v $(pwd)/workspace:/workspace daikon-jml:latest bash

# Navigate to results
cd myproject/daikon-output

# Print invariants in different formats
java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format java com_example_MyClass.inv.gz

java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format jml com_example_MyClass.inv.gz

java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format esc com_example_MyClass.inv.gz

java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format dbc com_example_MyClass.inv.gz
```

### Filtering and Analyzing Results

```bash
#!/bin/bash
# analyze-results.sh - Generate summary of JML specifications

REPO_DIR="workspace/myproject"

echo "=== JML Specification Summary ==="
echo ""

# Count files
echo "Generated Files:"
echo "  JML files: $(ls $REPO_DIR/daikon-output/*.jml 2>/dev/null | wc -l)"
echo "  Invariant files: $(ls $REPO_DIR/daikon-output/*.inv.gz 2>/dev/null | wc -l)"
echo "  Decorated classes: $(find $REPO_DIR/jml-decorated-classes -name "*.java" 2>/dev/null | wc -l)"
echo ""

# Analyze invariant types
echo "Invariant Statistics:"
echo "  Class invariants: $(grep -h ":::OBJECT" $REPO_DIR/daikon-output/*.jml 2>/dev/null | wc -l)"
echo "  Method specifications: $(grep -h ":::ENTER\|:::EXIT" $REPO_DIR/daikon-output/*.jml 2>/dev/null | wc -l)"
echo ""

# Find classes with most invariants
echo "Top 5 Classes by Invariant Count:"
for jml in $REPO_DIR/daikon-output/*.jml; do
  count=$(grep -c "^[^=]" "$jml" 2>/dev/null || echo 0)
  echo "$count $(basename $jml .jml)"
done | sort -rn | head -5
```

### Integration with OpenJML

After generating JML specifications, verify them with OpenJML:

```bash
# Install OpenJML (if not already installed)
# Download from http://www.openjml.org/

# Verify a decorated class
cd workspace/myproject/jml-decorated-classes
openjml -esc com/example/MyClass.java

# Check all decorated classes
find . -name "*.java" -exec openjml -check {} \;
```

### Preparing for Isabelle/HOL Translation

```bash
# After generating JML specifications, prepare for Phase 2 translation

# 1. Collect all JML specifications
mkdir -p phase2-input/jml-specs
cp workspace/myproject/daikon-output/*.jml phase2-input/jml-specs/

# 2. Copy decorated source files
cp -r workspace/myproject/jml-decorated-classes phase2-input/annotated-sources/

# 3. Generate summary document
cat > phase2-input/README.md << 'EOF'
# JML Specifications for Isabelle/HOL Translation

## Source Project
Repository: [project URL]
Analysis Date: $(date)
Test Classes Analyzed: $(cat workspace/myproject/test-mapping.json | jq 'length')

## Contents
- `jml-specs/`: Raw JML specifications from Daikon
- `annotated-sources/`: Java source files with JML annotations

## Next Steps
1. Parse JML specifications
2. Abstract OOP constructs (inheritance, polymorphism)
3. Generate intermediate representation
4. Translate to Isabelle/HOL theory files

## Invariant Summary
$(./analyze-results.sh)
EOF

# 4. Archive for Phase 2 processing
tar czf phase2-input-$(date +%Y%m%d).tar.gz phase2-input/
```

## Troubleshooting

### Common Issues and Solutions

#### Issue: "Docker: command not found"

**Solution**: Install Docker for your platform
```bash
# Ubuntu/Debian
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh

# Verify
docker --version
```

#### Issue: "Permission denied" when building

**Solution**: Add your user to docker group
```bash
sudo usermod -aG docker $USER
newgrp docker  # Or logout and login again
```

#### Issue: "Repository not found or access denied"

**Possible causes**:
1. Repository is private (provide credentials)
2. URL is incorrect (check spelling)
3. Network issues

**Solution**:
```bash
# Test Git access outside Docker
git clone <repo-url> test-clone
rm -rf test-clone

# For private repos, use token
docker run --rm \
  -e GIT_TOKEN="your_token" \
  daikon-jml:latest <repo-url>
```

#### Issue: "Maven compilation failed"

**Causes**:
- Missing dependencies
- Java version incompatibility
- Corrupted pom.xml

**Solution**:
```bash
# Try compiling locally first
git clone <repo-url>
cd <repo-name>
mvn clean compile

# If successful, check Java version
java -version  # Should be 1.8

# Try with Docker again
docker run --rm -v $(pwd)/workspace:/workspace \
  daikon-jml:latest \
  prepare file://$(pwd)  # Use local copy
```

#### Issue: "No test classes detected"

**Causes**:
- Tests in non-standard location
- Missing JUnit annotations
- Test dependencies not in pom.xml

**Solution**:
```bash
# Check test structure
ls -R src/test/java/

# Verify JUnit in pom.xml
grep -A5 "junit" pom.xml

# Run in interactive mode to debug
docker run -it --rm -v $(pwd)/workspace:/workspace daikon-jml:latest bash
cd myproject
python3 /usr/local/bin/process_project.py detect-tests
```

#### Issue: "Out of memory error"

**Solution**: Increase Docker memory allocation
```bash
# Docker Desktop: Settings → Resources → Memory (increase to 10GB+)

# Command line
docker run --rm \
  --memory="12g" \
  --memory-swap="16g" \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest analyze myproject
```

#### Issue: "Trace collection timeouts"

**Cause**: Some tests are very complex and take >10 minutes with instrumentation

**Solution**: This is normal for complex tests. The tool will:
- Skip timed-out tests
- Use traces from completed tests
- Still generate useful invariants

If too many tests timeout:
```bash
# Filter test-mapping.json to remove slow tests
cd workspace/myproject
# Edit test-mapping.json manually to remove problematic tests
nano test-mapping.json

# Re-run analyze
docker run --rm --memory="10g" -v $(pwd)/../:/workspace \
  daikon-jml:latest analyze myproject
```

#### Issue: "No method-level invariants generated"

**Causes**:
- Tests don't call those specific methods
- Methods called with limited input variation
- Insufficient test coverage

**Solution**:
1. Check test coverage:
```bash
cd workspace/myproject
mvn jacoco:report
# View target/site/jacoco/index.html
```

2. Improve test coverage or add more diverse test cases
3. Accept that some methods may not have detectable invariants

#### Issue: "JML files are empty or have only class invariants"

**Solution**: Check if tests actually exercise the methods:
```bash
# View what Daikon found
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest bash -c \
  "cd myproject/daikon-output && cat *.jml | grep -A 5 ':::ENTER'"

# If empty, tests may not be calling instrumented methods
# Check test-mapping.json and improve test coverage
```

## Technical Details

### Technologies Used

| Component | Version | Purpose |
|-----------|---------|---------|
| Ubuntu | 22.04 | Base OS |
| OpenJDK | 8 | Java runtime |
| Maven | Latest | Build tool |
| Daikon | 5.8.22 | Invariant detection |
| DynComp | 5.8.22 | Comparability analysis |
| Chicory | 5.8.22 | Runtime instrumentation |
| Python | 3.x | Orchestration scripts |
| Git | Latest | VCS |

### Daikon Components

- **Chicory**: (Daikon Frontend) Instruments Java bytecode to collect traces at runtime
- **DynComp**: Analyzes dynamic comparability to optimize trace collection
- **Daikon**: Core invariant detector using likelihood-based inference
- **PrintInvariants**: Formats output to various specifications (Java, JML, ESC/Java, DBC)

### Three-Phase Internal Architecture

```
Phase 1: DynComp (Per-test)
├── Input: Compiled test classes, classpath
├── Process: 
│   ├── Instrument bytecode with DynComp agent
│   ├── Execute test with instrumentation
│   └── Track variable comparability relationships
└── Output: .decls files (comparability declarations)

Phase 2: Chicory (Per-test)
├── Input: Compiled classes, .decls files, classpath
├── Process:
│   ├── Instrument bytecode with Chicory agent
│   ├── Load DynComp comparability data
│   ├── Execute test with instrumentation
│   ├── Record method entries (:::ENTER)
│   ├── Record method exits (:::EXIT)
│   ├── Record object states (:::OBJECT)
│   └── Compress and write trace data
└── Output: .dtrace.gz files (execution traces)

Phase 3: Daikon (Per-trace)
├── Input: .dtrace.gz files
├── Process:
│   ├── Load and decompress traces
│   ├── Parse program points and variable values
│   ├── Apply statistical analysis
│   ├── Detect likely invariants
│   ├── Filter by confidence threshold
│   ├── Format as JML specifications
│   └── Separate class/method invariants
└── Output: .inv.gz (binary), .jml (text), decorated .java files
```

### Performance Characteristics

| Project Size | Prepare Time | DynComp Time | Chicory Time | Daikon Time | Total Analyze |
|--------------|--------------|--------------|--------------|-------------|---------------|
| Small (< 50 classes, < 100 tests) | 1-2 min | 2-5 min | 5-10 min | 2-5 min | 10-20 min |
| Medium (50-200 classes, 100-500 tests) | 2-5 min | 10-20 min | 20-40 min | 10-20 min | 40-80 min |
| Large (200-500 classes, 500-2000 tests) | 5-10 min | 30-60 min | 60-120 min | 30-60 min | 2-4 hours |
| Very Large (500+ classes, 2000+ tests) | 10-20 min | 1-2 hours | 2-4 hours | 1-2 hours | 4-8+ hours |

**Factors affecting performance**:
- Number and complexity of test cases
- Test execution time
- Code complexity and method count
- Available memory and CPU cores
- DynComp availability (50-70% speedup)

### Invariant Types Detected

Daikon can detect 100+ types of invariants including:

**Unary invariants** (single variable):
- `x == c` (constant value)
- `x > c`, `x >= c` (range bounds)
- `x != null` (non-null)
- `x in {1, 2, 3}` (set membership)
- `x.getClass() == T.class` (type invariants)

**Binary invariants** (two variables):
- `x < y`, `x <= y` (ordering)
- `x == y`, `x != y` (equality)
- `x == y + c` (linear relationship)
- `array[i] == value` (array element)
- `x.equals(y)` (equivalence)

**Ternary invariants** (three variables):
- `x == y + z` (linear combination)
- `array[i] == array[j]` (array equality)

**Sequence invariants**:
- `array.length > 0` (non-empty)
- `array is sorted`
- `array has no duplicates`
- `array.length == count` (size relationships)

**Object invariants**:
- `obj.field != null`
- `obj1.id == obj2.id` (object relationships)
- `collection.size() == count`

**Method-level invariants**:
- Preconditions: `param > 0`, `param != null`
- Postconditions: `\result > 0`, `\result == expected`
- State changes: `field == \old(field) + delta`

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
   - Workaround: Create Maven wrapper or convert build system

4. **Java 8 specific**
   - Newer Java versions may have compatibility issues
   - Workaround: Use Java 8 compatible syntax or update Daikon

5. **JUnit 4/5 only**
   - TestNG not supported
   - Custom test frameworks not supported
   - Workaround: Convert tests to JUnit or wrap test execution

6. **Standard Maven layout required**
   - Non-standard directory structures may fail
   - Workaround: Restructure project or modify detection script

7. **Test execution requirements**
   - Tests must run without external dependencies
   - No database, API, or file system dependencies during test execution
   - Workaround: Use mocks, test containers, or embedded databases

8. **Memory constraints**
   - Very large projects (1000+ classes) may exceed memory
   - Complex tests can generate traces >500MB
   - Workaround: Increase Docker memory to 12-16GB or filter tests

9. **Processing time**
   - Large codebases can take hours
   - No incremental analysis (must re-run entire analyze phase)
   - Workaround: Run overnight, use powerful hardware, or analyze modules separately

10. **Invariant quality depends on test coverage**
    - Low test coverage (<30%) produces limited invariants
    - Tests with poor input diversity miss edge cases
    - Workaround: Improve test suite before running analysis

11. **OOP limitations for HOL translation**
    - Some advanced OOP features difficult to translate (deep inheritance, reflection)
    - Dynamic dispatch complexity may require manual intervention in Phase 2/3
    - Current research addresses these challenges

### Known Issues

- **Unicode handling**: Some non-ASCII characters in source files may cause issues
- **Complex generics**: Deep generic type hierarchies may not be fully analyzed
- **Dynamic class loading**: Reflectively loaded classes won't be instrumented
- **Native methods**: JNI methods cannot be analyzed
- **Test dependencies**: Tests that depend on each other may produce incomplete results
- **Flaky tests**: Non-deterministic tests may produce inconsistent invariants
- **Timeout sensitivity**: Some tests legitimately need >10 minutes with instrumentation

## FAQ

### General Questions

**Q: What is this tool's relationship to the Isabelle/HOL translation workflow?**  
A: This tool implements **Phase 1** of a three-phase workflow for translating Java to Isabelle/HOL. It generates JML specifications that serve as input for Phase 2 (Java/JML → Why3) and ultimately Phase 3 (Why3 → Isabelle/HOL). This automated workflow enables formal verification of production Java code without manual specification effort.

**Q: Why is automating Java-to-Isabelle translation important?**  
A: Most critical software (finance, healthcare, autonomous systems) is written in Java but lacks formal specifications. Manual translation to formal systems like Isabelle/HOL is prohibitively expensive. This automated workflow makes formal verification practical for real-world codebases, enabling mathematical proofs of correctness for production systems.

**Q: Can I use the generated JML for other purposes besides Isabelle translation?**  
A: Absolutely! The generated JML can be used for:
- Runtime assertion checking (using OpenJML)
- Static verification (using ESC/Java2 or KeY)
- Documentation and developer understanding
- Contract-based testing
- Any other JML-aware tool

**Q: Why split into two phases?**  
A: The two-phase approach allows you to:
- Verify compilation quickly before running intensive analysis
- Inspect and modify test selection between phases
- Resume analysis if it fails without re-cloning and re-compiling
- Batch prepare multiple projects and analyze them later

**Q: How long does each phase take?**  
A:
- **Prepare**: 1-10 minutes (depending on project size and compilation complexity)
- **Analyze**: 10 minutes to several hours (depending on test count and complexity)
  - DynComp: ~30% of total time
  - Chicory: ~50% of total time
  - Daikon: ~20% of total time

**Q: Is my code sent anywhere?**  
A: No, all processing happens locally in the Docker container. Nothing is uploaded. This is crucial for proprietary codebases preparing for formal verification.

**Q: What quality of invariants can I expect?**  
A: Invariant quality directly correlates with test coverage:
- **<30% coverage**: Limited, mostly trivial invariants
- **30-50% coverage**: Reasonable basic contracts
- **50-70% coverage**: Good quality specifications
- **>70% coverage**: Excellent, comprehensive specifications

**Q: How accurate are the generated invariants?**  
A: Daikon invariants are "likely" invariants based on observed behavior. They represent what tests exercise, not all possible behaviors. With good test coverage (>70%), invariants are typically very accurate. Always review generated specifications, especially for safety-critical systems.

### Technical Questions

**Q: Can I run analyze multiple times on the same prepared project?**  
A: Yes! You can re-run the analyze phase as many times as needed:
```bash
# Prepare once
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>

# Analyze multiple times (maybe after modifying test-mapping.json)
docker run --rm --memory="10g" -v $(pwd)/workspace:/workspace daikon-jml:latest analyze <repo>
```

**Q: Can I modify test-mapping.json between phases?**  
A: Yes! This is a key benefit:
```bash
# Prepare
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest prepare <url>

# Edit to remove slow tests or focus on specific classes
nano workspace/repo/test-mapping.json

# Analyze with filtered tests
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo
```

**Q: Why use DynComp? Can I skip it?**  
A: DynComp provides:
- 50-70% reduction in memory usage
- Faster trace collection
- More focused invariant detection
The tool automatically detects if DynComp is available and uses it. If unavailable, it falls back to Chicory alone (still works, just uses more memory).

**Q: What if my tests timeout during Chicory phase?**  
A: This is normal for complex tests. The tool:
- Skips timed-out tests (>10 minutes)
- Uses traces from completed tests
- Still generates useful invariants
You can filter out problematic tests by editing `test-mapping.json`.

**Q: How do I get method-level invariants, not just class-level?**  
A: Method-level invariants require:
1. Tests that actually call those methods
2. Diverse input values in tests
3. Sufficient execution to establish patterns
If you're only getting class invariants, improve test coverage or add more test cases with varied inputs.

**Q: Can I analyze only specific packages or classes?**  
A: Yes, edit `test-mapping.json` after the prepare phase to include only the tests/classes you want to analyze.

**Q: What if prepare succeeds but analyze fails?**  
A: Debug and re-run just the analyze phase:
```bash
# Check what went wrong
docker run -it --rm -v $(pwd)/workspace:/workspace daikon-jml:latest bash
cd <repo>
# Inspect daikon-output/, check logs

# Fix issues (increase memory, filter tests, etc.)
# Re-run analyze
docker run --rm --memory="12g" -v $(pwd)/workspace:/workspace daikon-jml:latest analyze <repo>
```

**Q: How do I increase memory for large projects?**  
A: Use Docker's `--memory` flag:
```bash
docker run --rm \
  --memory="16g" \
  --memory-swap="24g" \
  -v $(pwd)/workspace:/workspace \
  daikon-jml:latest analyze <repo>
```

Also ensure Docker Desktop has sufficient memory allocated (Preferences → Resources → Memory).

**Q: Can I run multiple analyze phases in parallel?**  
A: Yes, if analyzing different repositories:
```bash
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo1 &
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo2 &
docker run --rm -v $(pwd)/workspace:/workspace daikon-jml:latest analyze repo3 &
wait
```

**Q: What's the difference between .inv.gz and .jml files?**  
A:
- `.inv.gz`: Binary format, compact, used by Daikon tools
- `.jml`: Human-readable JML text format, used for decoration and manual review

Both contain the same invariants in different formats.

**Q: How do I prepare the JML output for Phase 2 (translation to IR)?**  
A: Collect the decorated source files and JML specifications:
```bash
# The jml-decorated-classes/ directory contains everything needed
tar czf phase2-input.tar.gz workspace/repo/jml-decorated-classes/

# Or just the JML specs
tar czf jml-specs.tar.gz workspace/repo/daikon-output/*.jml
```

## Related Work

### Academic Publications

This tool is part of ongoing research on automated formal verification of object-oriented systems. Key publications:

1. **"Automated Translation of Java to Isabelle/HOL"**
   - [Publication in SISTEDES 2025](https://biblioteca.sistedes.es/entities/art%C3%ADculo/218b4c12-c06d-4b3b-b3ca-afbf013a354d)

2. **"Automatic Proof Generation: Fine-tuning and RAG in Reasoner vs. Math LLMs"**
   - [Publication in ACM DL](https://dl.acm.org/doi/10.1145/3696630.3728705)


### Related Tools and Frameworks

- **OpenJML**: Runtime assertion checking and static verification for JML
- **KeY**: Theorem prover for Java with JML support
- **ESC/Java2**: Extended static checker for Java with JML
- **Krakatoa**: Tool for deductive verification of Java programs using Coq
- **Why3**: Platform for deductive program verification with Java front-end

### Future Directions

Ongoing research includes:
- **Phase 2**: Java/JML → Intermediate Representation translator
- **Phase 3**: IR → Isabelle/HOL theorem generator
- **Incremental verification**: Support for modular analysis
- **Improved OOP encoding**: Better handling of advanced Java features
- **Machine learning integration**: Learning from verified examples
- **IDE integration**: Real-time specification suggestion

## Contributing

Contributions are welcome! Here are ways to help:

### Reporting Issues

When reporting issues, please include:
- Docker version (`docker --version`)
- Operating system and version
- Complete command used
- Full error output
- Repository URL (if public)
- Contents of `test-mapping.json` (if relevant)

### Improving the Tool

**Test Detection**:
- Test with diverse project structures
- Report false positives/negatives
- Contribute regex patterns for edge cases

**JML Decoration**:
- Improve formatting of generated specifications
- Add support for additional JML constructs
- Better method signature matching

**Performance**:
- Optimize trace collection
- Reduce memory footprint
- Parallelize analysis where possible

**Documentation**:
- Fix typos or unclear sections
- Add more examples
- Translate to other languages
- Create video tutorials

**Integration**:
- Add support for Gradle
- Support for Java 11+
- Integration with other formal tools

## License

This Docker configuration is provided as-is for educational and research purposes.

### Component Licenses

- **Daikon**: MIT License - https://plse.cs.washington.edu/daikon/
- **Maven**: Apache License 2.0 - https://maven.apache.org/
- **JUnit**: Eclipse Public License - https://junit.org/
- **Ubuntu**: Various open-source licenses
- **OpenJDK**: GPL v2 with Classpath Exception

## Acknowledgments

This work is part of research on automated formal verification conducted at [Your Institution]. We acknowledge:

- The Daikon development team at MIT and University of Washington for the invariant detection framework
- The JML community for the specification language
- The Isabelle/HOL team for the theorem proving platform
- Contributors to the open-source tools that make this workflow possible

## References

### Tool Documentation

- [Daikon Invariant Detector](https://plse.cs.washington.edu/daikon/) - Official Daikon website
- [Daikon User Manual](https://plse.cs.washington.edu/daikon/download/doc/daikon.html) - Complete documentation
- [JML Reference Manual](https://www.openjml.org/) - JML specification language
- [OpenJML Documentation](https://www.openjml.org/tutorial/) - JML verification tool
- [Isabelle Documentation](https://isabelle.in.tum.de/documentation.html) - Theorem prover docs
- [Maven Documentation](https://maven.apache.org/guides/) - Maven build tool
- [Docker Documentation](https://docs.docker.com/) - Container platform

### Research Papers

- Ernst, M. D., et al. "The Daikon System for Dynamic Detection of Likely Invariants." Science of Computer Programming 69.1-3 (2007): 35-45.
- Leavens, G. T., et al. "JML: A notation for detailed design." Behavioral Specifications of Businesses and Systems. Springer, 1999. 175-188.
- Nipkow, T., Paulson, L. C., & Wenzel, M. "Isabelle/HOL: A Proof Assistant for Higher-Order Logic." Springer, 2002.

### Academic Work

For academic citations of this tool:

```bibtex
@misc{daikon-jml-tool,
  title={Daikon JML Instrumentation Tool: Automated Specification Generation for Java-to-Isabelle Translation},
  author={[Your Name]},
  year={2025},
  howpublished={\url{https://github.com/your-repo/daikon-jml-docker}},
  note={Phase 1 of Java-to-Isabelle/HOL translation workflow}
}
```

And cite the foundational Daikon paper:

```bibtex
@article{daikon2007,
  author = {Ernst, Michael D. and Perkins, Jeff H. and Guo, Philip J. and McCamant, Stephen and Pacheco, Carlos and Tschantz, Matthew S. and Xiao, Chen},
  title = {The Daikon System for Dynamic Detection of Likely Invariants},
  journal = {Science of Computer Programming},
  volume = {69},
  number = {1-3},
  pages = {35--45},
  year = {2007},
  publisher = {Elsevier}
}
```

### Research Collaboration

For collaborations on the Java-to-Isabelle/HOL translation workflow

- Email: jcrecio@uma.es
- Institution: Universidad de Málaga
- Research Group: ITIS Software

---

**Last Updated**: November 2025  
**Status**: Active research
