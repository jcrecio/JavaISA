# Daikon JML Instrumentation Docker Tool

A comprehensive Docker-based tool for automatically analyzing Java Maven projects using the Daikon invariant detector and generating JML (Java Modeling Language) specifications.

## Table of Contents

- [Overview](#overview)
- [What This Tool Does](#what-this-tool-does)
- [Prerequisites](#prerequisites)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Detailed Usage](#detailed-usage)
- [Pipeline Architecture](#pipeline-architecture)
- [Output Structure](#output-structure)
- [Configuration Options](#configuration-options)
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

The tool is particularly useful for:
- **Software verification**: Generate formal specifications for existing code
- **Documentation**: Automatically document behavioral contracts
- **Reverse engineering**: Understand implicit constraints in legacy code
- **Testing**: Verify that code behavior matches expected invariants

## What This Tool Does

### Step-by-Step Process

1. **Repository Cloning**: Downloads your Java project from GitHub
2. **Compilation Verification**: Ensures the project builds successfully with Maven
3. **Test Discovery**: Intelligently identifies all JUnit test classes (both JUnit 4 and 5)
4. **Test Mapping**: Analyzes test code to determine which production classes each test exercises
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

### Option 1: Build from Source

1. **Clone or download these files** to a directory:
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

### Option 2: Pre-built Image (if available)

```bash
docker pull your-registry/daikon-jml:latest
```

## Quick Start

### Analyze a GitHub Repository

```bash
docker run --rm daikon-jml:latest https://github.com/username/project.git
```

### Save Results to Your Machine

```bash
# Create output directory
mkdir -p ./analysis-output

# Run analysis and mount output directory
docker run --rm \
  -v $(pwd)/analysis-output:/workspace \
  daikon-jml:latest \
  https://github.com/username/project.git
```

After completion, check `./analysis-output/project-name/` for results.

## Detailed Usage

### Basic Command Structure

```bash
docker run [DOCKER_OPTIONS] daikon-jml:latest [REPOSITORY_URL]
```

### Docker Options Explained

#### Volume Mounting (Persist Results)

```bash
-v /host/path:/workspace
```

Maps a directory on your machine to the container's workspace. Results persist after container stops.

**Example**:
```bash
docker run --rm -v $(pwd)/output:/workspace daikon-jml:latest https://github.com/user/repo.git
```

#### Interactive Mode (For Debugging)

```bash
docker run -it --rm daikon-jml:latest bash
```

Starts a shell inside the container for manual execution and debugging.

**Inside the container**:
```bash
/usr/local/bin/entrypoint.sh https://github.com/user/repo.git
```

#### Remove Container After Completion

```bash
--rm
```

Automatically removes the container after it finishes (recommended to save disk space).

#### Named Container (For Long-Running Analysis)

```bash
--name my-analysis
```

Gives your container a specific name for easier reference.

**Example**:
```bash
docker run --name java-analysis -v $(pwd)/output:/workspace daikon-jml:latest https://github.com/user/repo.git

# Check status
docker ps -a | grep java-analysis

# View logs
docker logs java-analysis
```

### Environment Variables

You can customize behavior with environment variables:

```bash
docker run --rm \
  -e MAVEN_OPTS="-Xmx4g" \
  -e DAIKON_MEMORY="2g" \
  -v $(pwd)/output:/workspace \
  daikon-jml:latest \
  https://github.com/user/repo.git
```

## Pipeline Architecture

### Complete Pipeline Flow

```
┌─────────────────────────────────────────────────────────────┐
│  1. CLONE REPOSITORY                                        │
│     - git clone from GitHub                                 │
│     - Validates repository accessibility                    │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  2. COMPILE PROJECT                                         │
│     - mvn clean compile                                     │
│     - Validates pom.xml and dependencies                    │
│     - Ensures Java 8 compatibility                          │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  3. DETECT TEST CLASSES                                     │
│     - Scans src/test/java/**/*.java                         │
│     - Identifies JUnit 4/5 tests                            │
│     - Detects @Test annotations                             │
│     - Finds test class naming patterns                      │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  4. MAP TESTS TO CLASSES                                    │
│     - Analyzes import statements                            │
│     - Tracks class instantiations                           │
│     - Builds test → production class mapping                │
│     - Outputs: test-mapping.json                            │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  5. COMPILE TESTS                                           │
│     - mvn test-compile                                      │
│     - Ensures test classes build correctly                  │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  6. INSTRUMENT WITH DAIKON                                  │
│     - Identifies classes to instrument                      │
│     - Prepares Chicory configuration                        │
│     - Sets up trace file locations                          │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  7. RUN TESTS WITH DAIKON                                   │
│     - Executes each test class with Chicory                 │
│     - Collects runtime traces (.dtrace.gz)                  │
│     - Records variable values and relationships             │
│     - Generates invariant files (.inv.gz)                   │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  8. GENERATE JML SPECIFICATIONS                             │
│     - Converts invariants to JML format                     │
│     - Parses invariant relationships                        │
│     - Formats as JML annotations                            │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│  9. DECORATE SOURCE FILES                                   │
│     - Reads original .java files                            │
│     - Inserts JML comments                                  │
│     - Preserves original formatting                         │
│     - Saves to jml-decorated-classes/                       │
└─────────────────────────────────────────────────────────────┘
```

### Component Details

#### Test Detection Algorithm

The tool identifies test classes using multiple heuristics:

1. **Location**: Files in `src/test/java/` directory
2. **Imports**: Presence of JUnit imports
   ```java
   import org.junit.Test;
   import org.junit.jupiter.api.Test;
   ```
3. **Annotations**: Methods annotated with `@Test`
4. **Naming**: Classes ending with `Test`, `Tests`, or `TestCase`

#### Test-to-Class Mapping

The mapping process:

1. Extracts all imports from test files
2. Filters out JUnit and Java standard library imports
3. Analyzes test method bodies for class instantiations
4. Matches against production classes in `src/main/java/`
5. Creates bidirectional mapping in `test-mapping.json`

**Example Mapping**:
```json
{
  "com.example.CalculatorTest": {
    "test_file": "src/test/java/com/example/CalculatorTest.java",
    "tested_classes": [
      "com.example.Calculator",
      "com.example.MathUtils"
    ]
  }
}
```

#### Daikon Instrumentation

Uses Chicory, Daikon's front-end for Java:

1. **Bytecode instrumentation**: Modifies compiled classes at runtime
2. **Value tracking**: Records variable values at program points
3. **Trace generation**: Creates `.dtrace.gz` files with execution traces
4. **Invariant inference**: Analyzes traces to discover likely invariants

## Output Structure

After successful execution, the repository directory contains:

```
<repository-name>/
│
├── src/                          # Original source (unchanged)
│   ├── main/java/
│   └── test/java/
│
├── target/                       # Maven build output
│   ├── classes/
│   └── test-classes/
│
├── daikon-output/                # Daikon analysis results
│   ├── com_example_Calculator.dtrace.gz      # Execution traces
│   ├── com_example_Calculator.inv.gz         # Binary invariants
│   ├── com_example_Calculator.jml            # JML format invariants
│   └── ...
│
├── instrumented-classes/         # Instrumentation metadata
│   └── classes-to-instrument.txt # List of instrumented classes
│
├── jml-decorated-classes/        # Enhanced source files
│   └── com/example/
│       ├── Calculator.java       # With JML annotations
│       └── MathUtils.java
│
└── test-mapping.json            # Test-to-class mapping
```

### File Format Details

#### test-mapping.json

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

Binary invariant files with:
- Discovered invariants
- Confidence levels
- Statistical evidence
- Invariant types

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

## Configuration Options

### Maven Configuration

If your project needs specific Maven settings, modify the Dockerfile:

```dockerfile
# Add custom Maven settings
COPY settings.xml /root/.m2/settings.xml
```

### Daikon Memory Settings

For large projects, increase Daikon's memory:

Edit `entrypoint.sh`:
```bash
export JAVA_OPTS="-Xmx4g -Xms1g"
```

Or pass via environment:
```bash
docker run -e JAVA_OPTS="-Xmx4g" daikon-jml:latest <repo-url>
```

### Selective Class Instrumentation

To instrument only specific packages, modify `process_project.py`:

```python
def should_instrument_class(self, class_name: str) -> bool:
    # Only instrument classes in specific package
    return class_name.startswith('com.mycompany.core')
```

## Examples

### Example 1: Simple Calculator Project

```bash
# Analyze a calculator project
docker run --rm -v $(pwd)/results:/workspace \
  daikon-jml:latest \
  https://github.com/example/simple-calculator.git

# View results
cd results/simple-calculator/jml-decorated-classes
ls -R
```

**Expected Output**:
```
com/example/
├── Calculator.java      # With JML: ensures result == a + b
├── Division.java        # With JML: requires divisor != 0
└── MathUtils.java       # With JML: class invariants
```

### Example 2: Apache Commons Lang

```bash
# Analyze a real-world project (may take 30+ minutes)
docker run --rm \
  -v $(pwd)/commons-analysis:/workspace \
  -e MAVEN_OPTS="-Xmx4g" \
  daikon-jml:latest \
  https://github.com/apache/commons-lang.git

# Check results
du -sh commons-analysis/commons-lang/daikon-output/
cat commons-analysis/commons-lang/test-mapping.json | jq
```

### Example 3: Private Repository with Credentials

```bash
# For private repos, use GitHub token
docker run --rm \
  -v $(pwd)/output:/workspace \
  -e GIT_USERNAME="your-username" \
  -e GIT_TOKEN="your-personal-access-token" \
  daikon-jml:latest \
  https://github.com/private-org/private-repo.git
```

Note: Modify `entrypoint.sh` to use credentials:
```bash
if [ -n "$GIT_TOKEN" ]; then
  git config --global credential.helper store
  echo "https://${GIT_USERNAME}:${GIT_TOKEN}@github.com" > ~/.git-credentials
fi
```

### Example 4: Analyzing Multiple Projects

```bash
#!/bin/bash
# analyze-multiple.sh

REPOS=(
  "https://github.com/user/project1.git"
  "https://github.com/user/project2.git"
  "https://github.com/user/project3.git"
)

for repo in "${REPOS[@]}"; do
  echo "Analyzing: $repo"
  docker run --rm \
    -v $(pwd)/batch-results:/workspace \
    daikon-jml:latest \
    "$repo"
done

echo "All analyses complete!"
ls -la batch-results/
```

### Example 5: Continuous Integration

`.github/workflows/daikon-analysis.yml`:
```yaml
name: Daikon Analysis

on:
  push:
    branches: [ main ]

jobs:
  analyze:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Build Daikon Image
        run: docker build -t daikon-jml .
        working-directory: ./daikon-docker
      
      - name: Run Analysis
        run: |
          docker run --rm \
            -v ${{ github.workspace }}/results:/workspace \
            daikon-jml:latest \
            https://github.com/${{ github.repository }}.git
      
      - name: Upload Results
        uses: actions/upload-artifact@v3
        with:
          name: daikon-results
          path: results/
```

## Advanced Usage

### Extracting Specific Invariants

```bash
# Run analysis
docker run --rm -v $(pwd)/output:/workspace \
  daikon-jml:latest \
  https://github.com/user/repo.git

# Extract method preconditions
cd output/repo-name/daikon-output
zcat *.inv.gz | grep "requires"

# Extract class invariants
zcat *.inv.gz | grep "invariant"

# View specific class
zcat com_example_MyClass.inv.gz | less
```

### Using Daikon Print Tools

Access Daikon's printing utilities:

```bash
# Start interactive container
docker run -it --rm -v $(pwd)/output:/workspace daikon-jml:latest bash

# Navigate to results
cd /workspace/repo-name/daikon-output

# Print invariants in different formats
java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format java com_example_MyClass.inv.gz

java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format jml com_example_MyClass.inv.gz

java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format dbc com_example_MyClass.inv.gz
```

### Filtering Invariants

Modify `process_project.py` to filter invariants:

```python
def filter_invariants(self, invariants: str) -> str:
    """Keep only high-confidence invariants."""
    filtered = []
    for line in invariants.split('\n'):
        # Keep only invariants with confidence > 0.99
        if 'confidence=1.0' in line or 'confidence=0.99' in line:
            filtered.append(line)
    return '\n'.join(filtered)
```

### Custom JML Templates

Create custom JML output formats:

```python
def format_jml_specification(self, class_name: str, invariants: List[str]) -> str:
    """Generate formatted JML specification."""
    template = f"""
/**
 * Formal specification for {class_name}
 * Generated: {datetime.now().isoformat()}
 * Tool: Daikon {self.daikon_version}
 */
/*@
 * Class Invariants:
{self._format_invariants(invariants, '  * ')}
 *
 * @specification-for {class_name}
 */
"""
    return template
```

### Integration with Other Tools

#### OpenJML Verification

```bash
# After generating JML
docker run --rm -v $(pwd)/output:/workspace daikon-jml:latest <repo>

# Verify with OpenJML
cd output/repo-name/jml-decorated-classes
openjml -esc com/example/MyClass.java
```

#### ESC/Java2 Extended Static Checking

```bash
# Convert JML to ESC/Java2 format
java -cp $DAIKONDIR/daikon.jar daikon.PrintInvariants \
  --format esc \
  myclass.inv.gz > myclass.esc
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
docker run --rm -v $(pwd)/output:/workspace \
  daikon-jml:latest \
  file://$(pwd)  # Use local copy
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
docker run -it --rm daikon-jml:latest bash
# Then manually check tests
```

#### Issue: "Daikon produces no invariants"

**Causes**:
- Tests don't execute target classes
- Tests fail during execution
- Insufficient test coverage

**Solution**:
```bash
# Verify tests run successfully
mvn test

# Check test coverage
mvn jacoco:report

# Run with verbose Daikon output
# Modify entrypoint.sh to add --verbose flag
```

#### Issue: "Out of memory error"

**Solution**: Increase Docker memory allocation
```bash
# Docker Desktop: Settings → Resources → Memory (increase to 4GB+)

# Command line
docker run --rm \
  --memory="4g" \
  --memory-swap="8g" \
  -e MAVEN_OPTS="-Xmx3g" \
  -v $(pwd)/output:/workspace \
  daikon-jml:latest <repo-url>
```

#### Issue: "JML files are empty or incomplete"

**Causes**:
- Daikon didn't find enough patterns
- Tests have low coverage
- Invariants filtered out

**Solution**:
```bash
# Check raw invariant files
cd output/repo/daikon-output
zcat *.inv.gz | head -100

# Lower confidence threshold in process_project.py
# Or examine dtrace files
java -cp $DAIKONDIR/daikon.jar daikon.Chicory --help
```

### Debug Mode

Enable detailed logging:

```bash
# Modify entrypoint.sh
set -x  # Add at top of file

# Run with verbose output
docker run --rm daikon-jml:latest <repo-url> 2>&1 | tee analysis.log

# Review logs
less analysis.log
```

### Getting Help

1. **Check logs**: Review console output for error messages
2. **Inspect outputs**: Examine intermediate files (`test-mapping.json`, `.dtrace.gz`)
3. **Test manually**: Run steps individually in interactive mode
4. **Search issues**: Look for similar problems in Daikon documentation
5. **Report bugs**: Provide complete error output and repository URL

## Technical Details

### Technologies Used

| Component | Version | Purpose |
|-----------|---------|---------|
| Ubuntu | 22.04 | Base OS |
| OpenJDK | 8 | Java runtime |
| Maven | Latest | Build tool |
| Daikon | 5.8.18 | Invariant detection |
| Python | 3.x | Scripting |

### Daikon Components

- **Chicory**: Ins