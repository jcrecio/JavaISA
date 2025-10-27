#!/usr/bin/env python3

# -*- coding: utf-8 -*-
# Author: Juan Carlos Recio Abad
# Date: 2025-10-19

import os
import sys
import json
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Set


def print_flush(text):
    print(text, flush=True)


class DaikonJMLProcessor:
    def __init__(self):
        self.project_root = Path.cwd()
        self.src_main = self.project_root / "src" / "main" / "java"
        self.src_test = self.project_root / "src" / "test" / "java"
        self.target_classes = self.project_root / "target" / "classes"
        self.target_test_classes = self.project_root / "target" / "test-classes"
        self.daikon_output = self.project_root / "daikon-output"
        self.instrumented_dir = self.project_root / "instrumented-classes"
        self.jml_dir = self.project_root / "jml-decorated-classes"

        self.daikon_output.mkdir(exist_ok=True)
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

    def detect_tested_classes(self, test_file_info: Dict) -> Set[str]:
        """Detect which classes are being tested based on imports and usage."""
        content = test_file_info["file"].read_text(encoding="utf-8", errors="ignore")
        tested_classes = set()

        # Get all imported classes from the main source
        for imp in test_file_info["imports"]:
            if not any(x in imp for x in ["junit", "org.junit", "java.", "javax."]):
                tested_classes.add(imp)

        # Also check for class instantiations in the test
        class_instantiations = re.findall(r"new\s+(\w+)\s*\(", content)
        for cls in class_instantiations:
            if cls[0].isupper():  # Class names typically start with uppercase
                tested_classes.add(cls)

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

            tested = self.detect_tested_classes(test_info_item)

            for test_class in test_info_item["classes"]:
                test_fqn = f"{test_info_item['package']}.{test_class}"
                matched_classes = []

                for tested_cls in tested:
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
        _ = subprocess.run(
            ["mvn", "dependency:build-classpath", "-Dmdep.outputFile=cp.txt"],
            capture_output=True,
            text=True,
        )

        cp_file = self.project_root / "cp.txt"
        if cp_file.exists():
            classpath = cp_file.read_text().strip()
            cp_file.unlink()
            return f"{self.target_classes}:{self.target_test_classes}:{classpath}"

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

    def run_daikon_on_tests(self):
        """Run tests with Daikon to collect invariants."""
        print_flush("patata")
        print_flush("Reading test mapping...")
        with open("test-mapping.json", "r") as f:
            test_mapping = json.load(f)

        if not test_mapping:
            print_flush("No test classes found to run")
            return

        # Get classpath
        classpath = self.get_classpath()
        daikon_jar = os.path.join(os.environ["DAIKONDIR"], "daikon.jar")

        # Run tests with Chicory instrumentation
        for test_class in test_mapping.keys():
            print_flush(f"\nRunning Daikon on: {test_class}")

            dtrace_file = (
                self.daikon_output / f"{test_class.replace('.', '_')}.dtrace.gz"
            )

            # Run with Chicory
            cmd = [
                "java",
                "-cp",
                f"{daikon_jar}:{classpath}",
                "daikon.Chicory",
                "--daikon-online",
                f"--dtrace-file={dtrace_file}",
                "org.junit.runner.JUnitCore",
                test_class,
            ]

            print_flush(f"  Command: {' '.join(cmd)}")

            result = subprocess.run(cmd, capture_output=True, text=True)

            if result.returncode == 0 or "OK" in result.stdout:
                print_flush(f"  ✓ Collected invariants for {test_class}")
            else:
                print_flush(f"  ⚠ Warning: Test execution had issues")
                if result.stdout:
                    print_flush(f"  stdout: {result.stdout[:200]}")
                if result.stderr:
                    print_flush(f"  stderr: {result.stderr[:200]}")

        # Process dtrace files to generate invariants
        print_flush("\nGenerating invariants from trace files...")
        dtrace_files = list(self.daikon_output.glob("*.dtrace.gz"))

        for dtrace in dtrace_files:
            inv_file = dtrace.with_suffix("").with_suffix(".inv.gz")
            jml_file = dtrace.with_suffix("").with_suffix(".jml")

            cmd = [
                "java",
                "-cp",
                daikon_jar,
                "daikon.Daikon",
                "--format",
                "java",
                "--output",
                str(inv_file),
                str(dtrace),
            ]

            subprocess.run(cmd, capture_output=True)

            # Also generate JML format
            cmd_jml = [
                "java",
                "-cp",
                daikon_jar,
                "daikon.Daikon",
                "--format",
                "jml",
                "--output",
                str(jml_file),
                str(dtrace),
            ]

            subprocess.run(cmd_jml, capture_output=True)

            if inv_file.exists():
                print_flush(f"  ✓ Generated invariants: {inv_file.name}")

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
                cmd = [
                    "java",
                    "-cp",
                    daikon_jar,
                    "daikon.PrintInvariants",
                    "--format",
                    "jml",
                    str(inv_file),
                ]

                result = subprocess.run(cmd, capture_output=True, text=True)
                if result.stdout:
                    jml_file.write_text(result.stdout)
                    jml_files.append(jml_file)

        # Parse JML and decorate source files
        for cls_name in classes_to_decorate:
            # Find the source file
            cls_path = cls_name.replace(".", "/") + ".java"
            src_file = self.src_main / cls_path

            if not src_file.exists():
                print_flush(f"  ⚠ Source file not found: {src_file}")
                continue

            # Read original source
            original_content = src_file.read_text(encoding="utf-8", errors="ignore")

            # Find corresponding JML
            jml_content = self.find_jml_for_class(cls_name, jml_files)

            # Decorate the class
            decorated_content = self.decorate_class_with_jml(
                original_content, jml_content
            )

            # Save decorated version
            decorated_file = self.jml_dir / cls_path
            decorated_file.parent.mkdir(parents=True, exist_ok=True)
            decorated_file.write_text(decorated_content, encoding="utf-8")

            print_flush(f"  ✓ Decorated: {cls_name}")

    def find_jml_for_class(self, class_name: str, jml_files: List[Path]) -> str:
        """Find JML specifications for a specific class."""
        jml_specs = []

        for jml_file in jml_files:
            content = jml_file.read_text(encoding="utf-8", errors="ignore")
            if class_name in content:
                jml_specs.append(content)

        return "\n".join(jml_specs) if jml_specs else ""

    def decorate_class_with_jml(self, original_content: str, jml_content: str) -> str:
        """Add JML annotations to the original class."""
        if not jml_content:
            return original_content

        lines = original_content.split("\n")
        decorated_lines = []

        # Add JML comment header
        jml_header = [
            "/*@",
            " * JML specifications generated by Daikon",
            " * These represent dynamically detected invariants",
            " */",
        ]

        # Find class declaration and add JML before it
        in_class = False
        for i, line in enumerate(lines):
            if (
                re.match(r"\s*public\s+(class|interface|enum)\s+\w+", line)
                and not in_class
            ):
                # Add JML header before class
                decorated_lines.extend(jml_header)
                decorated_lines.append("/*@")
                decorated_lines.append(f" * Daikon invariants:")
                for jml_line in jml_content.split("\n")[:20]:  # Limit output
                    if jml_line.strip():
                        decorated_lines.append(f" * {jml_line.strip()}")
                decorated_lines.append(" */")
                in_class = True

            decorated_lines.append(line)

        return "\n".join(decorated_lines)


def main():
    if len(sys.argv) < 2:
        print_flush("Usage: process_project.py <command>")
        print_flush("Commands:")
        print_flush("  detect-tests     - Detect test classes and their targets")
        print_flush("  instrument-daikon - Prepare classes for Daikon instrumentation")
        print_flush("  run-daikon       - Run tests with Daikon to collect invariants")
        print_flush("  generate-jml     - Generate JML decorated classes")
        sys.exit(1)

    processor = DaikonJMLProcessor()
    command = sys.argv[1]

    if command == "detect-tests":
        processor.detect_tests()
    elif command == "instrument-daikon":
        processor.instrument_with_daikon()
    elif command == "run-daikon":
        print_flush("____debug")
        processor.run_daikon_on_tests()
    elif command == "generate-jml":
        processor.generate_jml_decorations()
    else:
        print_flush(f"Unknown command: {command}")
        sys.exit(1)


if __name__ == "__main__":
    main()
