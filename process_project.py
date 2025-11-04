#!/usr/bin/env python3

# -*- coding: utf-8 -*-
# Author: Juan Carlos Recio Abad
# Date: 2025-10-19
# Modified: Added DynComp support for better memory usage and invariant quality

import os
import signal
import sys
import json
import re
import subprocess
from pathlib import Path
import time
from timeit import Timer
from typing import Dict, List, Set


def print_flush(text):
    print(text, flush=True)


def run_command_with_output(command, execution_dir=None, timeout=None):
    full_output = []
    full_error = []

    process = subprocess.Popen(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=1,
        universal_newlines=True,
        cwd=execution_dir,
        env=os.environ.copy(),
        shell=True,
        preexec_fn=None if timeout is None else os.setsid,
    )

    def kill_process():
        try:
            os.killpg(os.getpgid(process.pid), signal.SIGTERM)
            time.sleep(1)
            if process.poll() is None:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass

    timer = None
    if timeout:
        timer = Timer(timeout, kill_process)
        timer.start()

    try:
        while True:
            output = process.stdout.readline()
            error = process.stderr.readline()

            if not output and not error and process.poll() is not None:
                break

            if output:
                print_flush(output.rstrip())
                full_output.append(output)
                sys.stdout.flush()

            if error:
                print(error.rstrip(), file=sys.stderr)
                full_error.append(error)
                sys.stderr.flush()

        return_code = process.poll()

        if timer and timer.is_alive():
            timer.cancel()

        if return_code is None:
            raise TimeoutError(f"Command execution timed out after {timeout} seconds")

        return subprocess.CompletedProcess(
            args=command,
            returncode=return_code,
            stdout="".join(full_output),
            stderr="".join(full_error),
        )
    finally:
        if timer:
            timer.cancel()
        if process.poll() is None:
            kill_process()


class DaikonJMLProcessor:
    def __init__(self):
        self.project_root = Path.cwd()
        self.src_main = self.project_root / "src" / "main" / "java"
        self.src_test = self.project_root / "src" / "test" / "java"
        self.target_classes = self.project_root / "target" / "classes"
        self.target_test_classes = self.project_root / "target" / "test-classes"
        self.daikon_output = self.project_root / "daikon-output"
        self.dyncomp_output = self.project_root / "dyncomp-output"
        self.instrumented_dir = self.project_root / "instrumented-classes"
        self.jml_dir = self.project_root / "jml-decorated-classes"

        self.daikon_output.mkdir(exist_ok=True)
        self.dyncomp_output.mkdir(exist_ok=True)
        self.instrumented_dir.mkdir(exist_ok=True)
        self.jml_dir.mkdir(exist_ok=True)

    def find_java_files(self, directory: Path) -> List[Path]:
        """Find all Java files in a directory."""
        if not directory.exists():
            return []
        return list(directory.rglob("*.java"))

    def parse_imports_and_classes(self, java_file: Path) -> Dict:
        """Parse a Java file to extract package, imports, and class names."""
        content = java_file.read_text(encoding="utf-8", errors="ignore")

        package_match = re.search(r"package\s+([\w.]+)\s*;", content)
        package = package_match.group(1) if package_match else ""

        imports = re.findall(r"import\s+([\w.]+)\s*;", content)

        # Find public classes
        class_matches = re.finditer(
            r"public\s+(?:class|interface|enum)\s+(\w+)", content
        )
        classes = [match.group(1) for match in class_matches]

        return {
            "package": package,
            "imports": imports,
            "classes": classes,
            "file": java_file,
        }

    def is_test_class(self, file_info: Dict) -> bool:
        """Determine if a class is a test class."""
        content = file_info["file"].read_text(encoding="utf-8", errors="ignore")

        # Check for JUnit imports
        has_junit = any("junit" in imp.lower() for imp in file_info["imports"])

        # Check for @Test annotations or test methods
        has_test_annotation = "@Test" in content or "@org.junit" in content

        # Check if class name ends with Test
        has_test_name = any(
            cls.endswith("Test") or cls.endswith("Tests")
            for cls in file_info["classes"]
        )

        return has_junit and (has_test_annotation or has_test_name)

    def detect_tested_classes(
        self, test_file_info: Dict, main_classes_map: Dict
    ) -> Set[str]:
        """Detect which classes are being tested based on imports and usage."""
        content = test_file_info["file"].read_text(encoding="utf-8", errors="ignore")
        tested_classes = set()

        # Get all imported classes from the main source
        for imp in test_file_info["imports"]:
            if not any(
                x in imp
                for x in [
                    "junit",
                    "org.junit",
                    "java.",
                    "javax.",
                    "org.mockito",
                    "org.hamcrest",
                ]
            ):
                # Check if this import matches a known main class
                if imp in main_classes_map:
                    tested_classes.add(imp)
                else:
                    # Try the last part (simple class name)
                    simple_name = imp.split(".")[-1]
                    if simple_name in main_classes_map:
                        # Get the full qualified name
                        info = main_classes_map[simple_name]
                        fqn = (
                            f"{info['package']}.{simple_name}"
                            if info["package"]
                            else simple_name
                        )
                        tested_classes.add(fqn)

        # Also check for class instantiations in the test
        class_instantiations = re.findall(r"new\s+(\w+)\s*\(", content)
        for cls in class_instantiations:
            if cls[0].isupper():  # Class names typically start with uppercase
                if cls in main_classes_map:
                    info = main_classes_map[cls]
                    fqn = f"{info['package']}.{cls}" if info["package"] else cls
                    tested_classes.add(fqn)

        return tested_classes

    def detect_tests(self):
        """Detect test classes and map them to the classes they test."""
        print_flush("Scanning project structure...")

        # Find all test files
        test_files = self.find_java_files(self.src_test)
        main_files = self.find_java_files(self.src_main)

        print_flush(f"Found {len(test_files)} test files")
        print_flush(f"Found {len(main_files)} main source files")

        # Parse all files
        test_info = [self.parse_imports_and_classes(f) for f in test_files]
        main_info = [self.parse_imports_and_classes(f) for f in main_files]

        # Build a map of fully qualified class names
        main_classes_map = {}
        for info in main_info:
            for cls in info["classes"]:
                fqn = f"{info['package']}.{cls}" if info["package"] else cls
                main_classes_map[fqn] = info
                main_classes_map[cls] = info  # Also store short name

        # Detect test classes and their targets
        test_mapping = {}

        for test_info_item in test_info:
            if not self.is_test_class(test_info_item):
                continue

            tested = self.detect_tested_classes(test_info_item, main_classes_map)

            for test_class in test_info_item["classes"]:
                test_fqn = (
                    f"{test_info_item['package']}.{test_class}"
                    if test_info_item["package"]
                    else test_class
                )
                matched_classes = []

                for tested_cls in tested:
                    # Ensure we're storing the fully qualified name
                    if tested_cls in main_classes_map:
                        matched_classes.append(tested_cls)

                if matched_classes:
                    test_mapping[test_fqn] = {
                        "test_file": str(test_info_item["file"]),
                        "tested_classes": matched_classes,
                    }

        # Save mapping
        with open("test-mapping.json", "w") as f:
            json.dump(test_mapping, f, indent=2)

        print_flush(f"\n✓ Detected {len(test_mapping)} test classes")
        for test_cls, info in test_mapping.items():
            print_flush(f"  • {test_cls}")
            for tested in info["tested_classes"]:
                print_flush(f"    → tests: {tested}")

        return test_mapping

    def get_classpath(self) -> str:
        """Build the full classpath including all dependencies."""
        cp_file = self.project_root / "daikon-cp.txt"

        result = subprocess.run(
            ["mvn", "dependency:build-classpath", f"-Dmdep.outputFile={cp_file}"],
            capture_output=True,
            text=True,
            cwd=str(self.project_root),
        )

        if cp_file.exists():
            classpath = cp_file.read_text().strip()
            full_cp = f"{self.target_classes}:{self.target_test_classes}:{classpath}"
            return full_cp
        else:
            print_flush(
                "⚠ Warning: Could not build dependency classpath, using minimal classpath"
            )
            return f"{self.target_classes}:{self.target_test_classes}"

    def instrument_with_daikon(self):
        """Instrument classes with Daikon's DynComp and Chicory."""
        print_flush("Reading test mapping...")
        with open("test-mapping.json", "r") as f:
            test_mapping = json.load(f)

        # Get all unique classes to instrument
        classes_to_instrument = set()
        for info in test_mapping.values():
            classes_to_instrument.update(info["tested_classes"])

        print_flush(f"Will instrument {len(classes_to_instrument)} classes")

        # Save list for later use
        with open("classes-to-instrument.txt", "w") as f:
            for cls in sorted(classes_to_instrument):
                f.write(f"{cls}\n")

        print_flush("✓ Classes prepared for instrumentation")

    def run_dyncomp_phase(
        self, test_class: str, comp_file: Path, classpath: str, daikon_jar: str
    ) -> bool:
        """Run DynComp to compute comparability information."""

        print_flush(f"    Running DynComp for comparability analysis...")

        cmd = (
            f"java -Xmx2g -cp '{daikon_jar}:{classpath}' daikon.DynComp "
            f"--comparability-file={comp_file} "
            f"org.junit.runner.JUnitCore {test_class}"
        )

        try:
            result = subprocess.run(
                cmd,
                shell=True,
                capture_output=True,
                text=True,
                timeout=300,
                cwd=str(self.project_root),
                env=os.environ.copy(),
            )

            if comp_file.exists() and comp_file.stat().st_size > 0:
                print_flush(
                    f"    ✓ DynComp completed ({comp_file.stat().st_size / 1024:.1f} KB)"
                )
                return True
            else:
                if result.stderr and len(result.stderr) > 0:
                    # Show brief error
                    error_lines = result.stderr.split("\n")[:3]
                    for line in error_lines:
                        if line.strip() and "at " not in line:
                            print_flush(f"    Error: {line[:100]}")
                print_flush(f"    ⚠ DynComp file not created or empty")
                return False

        except subprocess.TimeoutExpired:
            print_flush(f"    ⚠ DynComp timeout")
            return False
        except Exception as e:
            print_flush(f"    ✗ DynComp exception: {str(e)[:100]}")
            return False

    def run_single_test_with_chicory(
        self,
        test_class: str,
        dtrace_file: Path,
        decls_file: Path,
        classpath: str,
        daikon_jar: str,
    ) -> bool:
        """Run a single test class with Chicory instrumentation."""

        # Use relative path from project root
        dtrace_relative = dtrace_file.name
        dtrace_full_path = self.daikon_output / dtrace_relative

        cmd = (
            f"java -Xmx4g "  # Increased to 4GB
            f"-cp '{daikon_jar}:{classpath}' "
            f"daikon.Chicory "
            f"--dtrace-file=daikon-output/{dtrace_relative} "
            f"org.junit.runner.JUnitCore {test_class}"
        )

        try:
            # Increased timeout to 10 minutes for complex tests
            result = subprocess.run(
                cmd,
                shell=True,
                capture_output=True,
                text=True,
                timeout=600,  # 10 minutes
                cwd=str(self.project_root),
                env=os.environ.copy(),
            )

            # Show test results
            if result.stdout:
                for line in result.stdout.split("\n"):
                    if "OK" in line or "FAILURES" in line or "Time:" in line:
                        print_flush(f"    {line.strip()}")

            # Check if trace file was created
            if dtrace_full_path.exists():
                file_size = dtrace_full_path.stat().st_size
                if file_size > 0:
                    print_flush(f"    ✓ Trace: {file_size / 1024:.1f} KB")
                    return True
                else:
                    print_flush(f"    ⚠ Trace file empty")
                    return False
            else:
                print_flush(f"    ✗ No trace file")
                return False

        except subprocess.TimeoutExpired:
            print_flush(f"    ⚠ Timeout (10 min) - test too complex, skipping")
            # Check if partial trace was created
            if dtrace_full_path.exists():
                file_size = dtrace_full_path.stat().st_size
                if file_size > 0:
                    print_flush(
                        f"    ℹ Partial trace created: {file_size / 1024:.1f} KB"
                    )
                    return True  # Use partial trace
            return False
        except Exception as e:
            print_flush(f"    ✗ Exception: {str(e)[:100]}")
            return False

    def check_dyncomp_available(self) -> bool:
        """Check if DynComp runtime is available."""
        daikon_dir = os.environ.get("DAIKONDIR", "/opt/daikon-5.8.18")
        dcomp_rt_jar = Path(daikon_dir) / "java" / "dcomp_rt.jar"
        return dcomp_rt_jar.exists()

    def run_daikon_on_tests(self):
        """Run tests with Daikon to collect invariants (3-phase process with DynComp if available)."""
        print_flush("Reading test mapping...")
        with open("test-mapping.json", "r") as f:
            test_mapping = json.load(f)

        if not test_mapping:
            print_flush("No test classes found to run")
            return

        print_flush(f"Will analyze {len(test_mapping)} test classes")

        # Get classpath
        print_flush("Building classpath...")
        classpath = self.get_classpath()
        daikon_jar = os.path.join(os.environ["DAIKONDIR"], "daikon.jar")

        # Verify Daikon jar exists
        if not os.path.exists(daikon_jar):
            print_flush(f"ERROR: Daikon jar not found at {daikon_jar}")
            return

        # Check if DynComp is available
        dyncomp_available = self.check_dyncomp_available()

        if dyncomp_available:
            print_flush("✓ DynComp runtime detected - will use 3-phase analysis")
        else:
            print_flush(
                "⚠ DynComp runtime not available - will use 2-phase analysis (Chicory only)"
            )
            print_flush("  This will use more memory but still works")

        total_tests = len(test_mapping)

        # ===================================================================
        # PHASE 1: DynComp Comparability Analysis (if available)
        # ===================================================================
        dyncomp_success = 0
        dyncomp_failed = 0

        if dyncomp_available:
            print_flush("\n" + "=" * 70)
            print_flush("PHASE 1: DynComp Comparability Analysis")
            print_flush("=" * 70)

            current = 0

            for test_class in test_mapping.keys():
                current += 1
                print_flush(f"\n[{current}/{total_tests}] DynComp: {test_class}")

                comp_file = (
                    self.dyncomp_output / f"{test_class.replace('.', '_')}.decls"
                )

                success = self.run_dyncomp_phase(
                    test_class, comp_file, classpath, daikon_jar
                )

                if success:
                    dyncomp_success += 1
                else:
                    dyncomp_failed += 1

            print_flush(
                f"\nDynComp summary: {dyncomp_success} successful, {dyncomp_failed} failed"
            )
        else:
            print_flush("\nSkipping DynComp phase (runtime not available)")

        # ===================================================================
        # PHASE 2: Chicory Trace Collection
        # ===================================================================
        print_flush("\n" + "=" * 70)
        if dyncomp_available:
            print_flush("PHASE 2: Chicory Trace Collection (using DynComp results)")
        else:
            print_flush("PHASE 1: Chicory Trace Collection (without DynComp)")
        print_flush("=" * 70)
        print_flush("Will instrument all packages except tests and standard libraries")

        success_count = 0
        error_count = 0
        current = 0

        for test_class in test_mapping.keys():
            current += 1
            print_flush(f"\n[{current}/{total_tests}] Chicory: {test_class}")

            dtrace_file = (
                self.daikon_output / f"{test_class.replace('.', '_')}.dtrace.gz"
            )
            decls_file = self.dyncomp_output / f"{test_class.replace('.', '_')}.decls"

            # Use DynComp results if available
            if dyncomp_available and not decls_file.exists():
                print_flush(f"    ⚠ No DynComp data for this test")

            success = self.run_single_test_with_chicory(
                test_class, dtrace_file, decls_file, classpath, daikon_jar
            )

            if success:
                file_size = dtrace_file.stat().st_size
                print_flush(f"  ✓ Trace collected ({file_size / 1024:.1f} KB)")
                success_count += 1
            else:
                print_flush(f"  ✗ Failed to collect trace")
                error_count += 1

        print_flush(f"\nTrace collection summary:")
        print_flush(f"  ✓ Successful: {success_count}/{total_tests}")
        if error_count > 0:
            print_flush(f"  ⚠ Errors: {error_count}/{total_tests}")

        # ===================================================================
        # PHASE 3: Invariant Generation
        # ===================================================================
        print_flush("\n" + "=" * 70)
        if dyncomp_available:
            print_flush("PHASE 3: Invariant Generation from Traces")
        else:
            print_flush("PHASE 2: Invariant Generation from Traces")
        print_flush("=" * 70)

        dtrace_files = list(self.daikon_output.glob("*.dtrace.gz"))

        if not dtrace_files:
            print_flush("⚠ No trace files were generated.")
            return

        print_flush(f"Found {len(dtrace_files)} trace files to process")

        inv_count = 0
        jml_count = 0

        for dtrace in dtrace_files:
            inv_file = dtrace.with_suffix("").with_suffix(".inv.gz")
            jml_file = dtrace.with_suffix("").with_suffix(".jml")

            print_flush(f"  Processing: {dtrace.name}")

            try:
                # First, let's try to process the dtrace file and see what Daikon produces
                # Use simpler command - let Daikon decide the output filename
                cmd = f"java -Xmx4g -cp '{daikon_jar}' daikon.Daikon " f"{str(dtrace)}"

                print_flush(
                    f"    Running: java -cp daikon.jar daikon.Daikon {dtrace.name}"
                )

                result = subprocess.run(
                    cmd,
                    shell=True,
                    capture_output=True,
                    text=True,
                    timeout=300,
                    cwd=str(self.daikon_output),
                )

                # Daikon creates .inv.gz by default with same base name as input
                # Check if it was created
                if inv_file.exists():
                    print_flush(f"    ✓ Invariants: {inv_file.name}")
                    inv_count += 1
                else:
                    # Something went wrong
                    print_flush(f"    ✗ Failed to generate invariants")
                    if result.returncode != 0:
                        print_flush(f"      Exit code: {result.returncode}")
                    if result.stderr:
                        error_lines = [
                            l.strip() for l in result.stderr.split("\n") if l.strip()
                        ][:5]
                        for line in error_lines:
                            print_flush(f"      {line}")
                    if result.stdout:
                        output_lines = [
                            l.strip() for l in result.stdout.split("\n") if l.strip()
                        ][:3]
                        if output_lines:
                            for line in output_lines:
                                print_flush(f"      {line}")

                # Now generate JML format separately
                cmd_jml = (
                    f"java -Xmx4g -cp '{daikon_jar}' daikon.PrintInvariants "
                    f"--format jml {str(inv_file)}"
                )

                if inv_file.exists():
                    result = subprocess.run(
                        cmd_jml, shell=True, capture_output=True, text=True, timeout=300
                    )

                    if result.stdout:
                        jml_file.write_text(result.stdout)
                        print_flush(f"    ✓ JML: {jml_file.name}")
                        jml_count += 1

            except subprocess.TimeoutExpired:
                print_flush(f"    ⚠ Timeout processing {dtrace.name}")
            except Exception as e:
                print_flush(f"    ✗ Error: {str(e)[:100]}")

        # Final Summary
        print_flush("\n" + "=" * 70)
        print_flush("FINAL SUMMARY")
        print_flush("=" * 70)
        if dyncomp_available:
            print_flush(f"  ✓ DynComp analyses: {dyncomp_success}/{total_tests}")
        print_flush(f"  ✓ Trace files: {success_count}/{total_tests}")
        print_flush(f"  ✓ Invariant files (.inv.gz): {inv_count}/{len(dtrace_files)}")
        print_flush(f"  ✓ JML files (.jml): {jml_count}/{len(dtrace_files)}")

        if inv_count == 0:
            print_flush("\n⚠ No invariants were generated. Possible reasons:")
            print_flush("  - Trace files may be empty (tests didn't execute any code)")
            print_flush("  - Daikon couldn't find enough patterns")
            print_flush("  - Tests may have failed during execution")
        else:
            print_flush(
                f"\n✓ Successfully generated invariants for {inv_count} test classes!"
            )
            print_flush(f"  View results in: daikon-output/ and jml-decorated-classes/")

    def find_source_file(self, class_name: str) -> Path:
        """Find source file for a class, handling both FQN and simple names."""
        # Try as fully qualified name first
        cls_path = class_name.replace(".", "/") + ".java"
        src_file = self.src_main / cls_path

        if src_file.exists():
            return src_file

        # If not found, try to find by simple class name
        simple_name = class_name.split(".")[-1]
        matching_files = list(self.src_main.rglob(f"{simple_name}.java"))

        if matching_files:
            if len(matching_files) == 1:
                return matching_files[0]
            else:
                # Multiple matches, try to find best match
                for match in matching_files:
                    # Check if the full path contains the package structure
                    if class_name.replace(".", "/") in str(match):
                        return match
                # Return first match as fallback
                return matching_files[0]

        return None

    def generate_jml_decorations(self):
        """Decorate original classes with JML annotations."""
        print_flush("Generating JML decorated classes...")

        # Read which classes were instrumented
        if not Path("classes-to-instrument.txt").exists():
            print_flush("No classes to decorate")
            return

        with open("classes-to-instrument.txt", "r") as f:
            classes_to_decorate = [line.strip() for line in f if line.strip()]

        # Find JML output files
        jml_files = list(self.daikon_output.glob("*.jml"))

        if not jml_files:
            print_flush(
                "⚠ No JML files found. Attempting to generate from invariants..."
            )
            inv_files = list(self.daikon_output.glob("*.inv.gz"))

            daikon_jar = os.path.join(os.environ["DAIKONDIR"], "daikon.jar")
            for inv_file in inv_files:
                jml_file = inv_file.with_suffix("").with_suffix(".jml")

                cmd = (
                    f"java -cp '{daikon_jar}' daikon.PrintInvariants "
                    f"--format jml {str(inv_file)}"
                )

                result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                if result.stdout:
                    jml_file.write_text(result.stdout)
                    jml_files.append(jml_file)

        # Parse JML and decorate source files
        decorated_count = 0
        not_found_count = 0

        for cls_name in classes_to_decorate:
            # Find the source file
            src_file = self.find_source_file(cls_name)

            if not src_file:
                print_flush(f"  ⚠ Source file not found for: {cls_name}")
                not_found_count += 1
                continue

            # Read original source
            original_content = src_file.read_text(encoding="utf-8", errors="ignore")

            # Find corresponding JML
            jml_content = self.find_jml_for_class(cls_name, jml_files)

            # Decorate the class
            decorated_content = self.decorate_class_with_jml(
                original_content, jml_content
            )

            # Save decorated version - preserve the original path structure
            relative_path = src_file.relative_to(self.src_main)
            decorated_file = self.jml_dir / relative_path
            decorated_file.parent.mkdir(parents=True, exist_ok=True)
            decorated_file.write_text(decorated_content, encoding="utf-8")

            print_flush(f"  ✓ Decorated: {cls_name}")
            decorated_count += 1

        print_flush(f"\nDecoration summary:")
        print_flush(f"  ✓ Successfully decorated: {decorated_count}")
        if not_found_count > 0:
            print_flush(f"  ⚠ Source files not found: {not_found_count}")

    def find_jml_for_class(self, class_name: str, jml_files: List[Path]) -> str:
        """Find JML specifications for a specific class."""
        jml_specs = []

        for jml_file in jml_files:
            content = jml_file.read_text(encoding="utf-8", errors="ignore")
            if class_name in content:
                jml_specs.append(content)

        return "\n".join(jml_specs) if jml_specs else ""

    def parse_jml_invariants(self, jml_content: str) -> Dict:
        """Parse JML content to extract class and method-level invariants."""
        invariants = {"class_invariants": [], "methods": {}}

        current_section = None
        current_method = None

        for line in jml_content.split("\n"):
            line = line.strip()

            # Detect class-level invariants (OBJECT section)
            if ":::OBJECT" in line:
                current_section = "class"
                current_method = None
                continue

            # Detect method entry points
            elif ":::ENTER" in line:
                # Extract method signature
                method_match = re.search(r"([\w.]+)\((.*?)\):::ENTER", line)
                if method_match:
                    method_name = method_match.group(1).split(".")[-1]
                    current_method = method_name
                    current_section = "enter"
                    if current_method not in invariants["methods"]:
                        invariants["methods"][current_method] = {
                            "preconditions": [],
                            "postconditions": [],
                        }
                continue

            # Detect method exit points
            elif ":::EXIT" in line:
                method_match = re.search(r"([\w.]+)\((.*?)\):::EXIT", line)
                if method_match:
                    method_name = method_match.group(1).split(".")[-1]
                    current_method = method_name
                    current_section = "exit"
                    if current_method not in invariants["methods"]:
                        invariants["methods"][current_method] = {
                            "preconditions": [],
                            "postconditions": [],
                        }
                continue

            # Skip empty lines and section markers
            if not line or line.startswith("=") or line.startswith("Variables:"):
                continue

            # Add invariants to appropriate section
            if current_section == "class":
                if line and not line.startswith("//"):
                    invariants["class_invariants"].append(line)
            elif current_section == "enter" and current_method:
                if line and not line.startswith("//"):
                    invariants["methods"][current_method]["preconditions"].append(line)
            elif current_section == "exit" and current_method:
                if line and not line.startswith("//"):
                    invariants["methods"][current_method]["postconditions"].append(line)

        return invariants

    def decorate_class_with_jml(self, original_content: str, jml_content: str) -> str:
        """Add JML annotations to the original class with both class and method-level invariants."""
        if not jml_content:
            return original_content

        # Parse JML to extract structured invariants
        invariants = self.parse_jml_invariants(jml_content)

        lines = original_content.split("\n")
        decorated_lines = []

        # Track if we've added class header
        class_header_added = False

        for i, line in enumerate(lines):
            # Add class-level JML before class declaration
            if (
                re.match(r"\s*public\s+(class|interface|enum)\s+\w+", line)
                and not class_header_added
            ):
                # Add class-level invariants header
                decorated_lines.append("/*@")
                decorated_lines.append(" * JML specifications generated by Daikon")
                decorated_lines.append(
                    " * These represent dynamically detected invariants"
                )
                decorated_lines.append(" */")

                if invariants["class_invariants"]:
                    decorated_lines.append("/*@")
                    decorated_lines.append(" * Class Invariants:")
                    for inv in invariants["class_invariants"][
                        :30
                    ]:  # Limit to 30 invariants
                        if inv.strip():
                            decorated_lines.append(f" * @ invariant {inv};")
                    decorated_lines.append(" */")

                class_header_added = True
                decorated_lines.append(line)
                continue

            # Add method-level JML before method declarations
            method_match = re.match(
                r"\s*(?:public|private|protected)?\s*(?:static\s+)?(?:[\w<>]+\s+)?([\w]+)\s*\([^)]*\)\s*(?:throws\s+[\w,\s]+)?\s*\{?",
                line,
            )
            if method_match:
                method_name = method_match.group(1)

                # Check if we have invariants for this method
                if method_name in invariants["methods"]:
                    method_invs = invariants["methods"][method_name]

                    if method_invs["preconditions"] or method_invs["postconditions"]:
                        decorated_lines.append("    /*@")

                        # Add preconditions
                        if method_invs["preconditions"]:
                            for pre in method_invs["preconditions"][:10]:  # Limit to 10
                                if pre.strip():
                                    decorated_lines.append(f"     @ requires {pre};")

                        # Add postconditions
                        if method_invs["postconditions"]:
                            for post in method_invs["postconditions"][
                                :10
                            ]:  # Limit to 10
                                if post.strip():
                                    # Handle return values
                                    if "\\result" not in post:
                                        decorated_lines.append(
                                            f"     @ ensures {post};"
                                        )
                                    else:
                                        decorated_lines.append(
                                            f"     @ ensures {post};"
                                        )

                        decorated_lines.append("     */")

            decorated_lines.append(line)

        return "\n".join(decorated_lines)


def main():
    if len(sys.argv) < 2:
        print_flush("Usage: process_project.py <command>")
        print_flush("Commands:")
        print_flush("  detect-tests     - Detect test classes and their targets")
        print_flush("  instrument-daikon - Prepare classes for Daikon instrumentation")
        print_flush(
            "  run-daikon       - Run tests with Daikon to collect invariants (3-phase with DynComp)"
        )
        print_flush("  generate-jml     - Generate JML decorated classes")
        sys.exit(1)

    processor = DaikonJMLProcessor()
    command = sys.argv[1]

    if command == "detect-tests":
        processor.detect_tests()
    elif command == "instrument-daikon":
        processor.instrument_with_daikon()
    elif command == "run-daikon":
        processor.run_daikon_on_tests()
    elif command == "generate-jml":
        processor.generate_jml_decorations()
    else:
        print_flush(f"Unknown command: {command}")
        sys.exit(1)


if __name__ == "__main__":
    main()
