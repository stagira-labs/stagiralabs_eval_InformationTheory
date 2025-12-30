#!/usr/bin/env python3
"""
Propagate @[target] decorators to dependent theorems/lemmas in Lean 4 files.

This script:
1. Finds all theorems/lemmas marked with @[target]
2. Identifies other theorems/lemmas that reference these targets in their proofs
3. Adds @[target] to those dependent theorems/lemmas

Usage:
    python propagate_targets.py <folder_path> [options]

Options:
    --dry-run        Show what would be changed without modifying files
    --quiet          Reduce output verbosity
    --include-defs   Include 'def' declarations (default: only theorem/lemma)

Example:
    python propagate_targets.py src/Mathlib/InformationTheory
    python propagate_targets.py src/Mathlib/RepresentationTheory
    python propagate_targets.py src/Mathlib/SetTheory --dry-run
"""

import os
import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Set, Dict, List, Tuple


@dataclass
class Declaration:
    """Represents a theorem/lemma/def declaration."""
    name: str
    kind: str  # 'theorem', 'lemma', 'def'
    has_target: bool
    line_start: int  # 0-indexed line where declaration starts (including attributes)
    line_decl: int   # 0-indexed line of the actual theorem/lemma/def keyword
    attr_line: int   # 0-indexed line of existing attributes, or -1 if none
    file_path: str
    proof_text: str  # The proof body text
    existing_attrs: str  # Existing attributes like "@[simp]"


def find_lean_files(folder: str) -> List[str]:
    """Recursively find all .lean files in a folder."""
    lean_files = []
    for root, _, files in os.walk(folder):
        for f in files:
            if f.endswith('.lean'):
                lean_files.append(os.path.join(root, f))
    return lean_files


def extract_declarations(file_path: str, include_defs: bool = True) -> List[Declaration]:
    """
    Extract all theorem/lemma/def declarations from a Lean file.

    Args:
        file_path: Path to the Lean file
        include_defs: Whether to include 'def' declarations (default True for target detection)

    Returns a list of Declaration objects with information about each declaration.
    """
    with open(file_path, 'r') as f:
        content = f.read()
        lines = content.split('\n')

    declarations = []

    # Pattern to match declaration with optional attributes
    # This matches: optional @[...] on preceding lines, then theorem/lemma/def name
    if include_defs:
        decl_pattern = re.compile(
            r'^(theorem|lemma|def)\s+(\w+)',
            re.MULTILINE
        )
    else:
        decl_pattern = re.compile(
            r'^(theorem|lemma)\s+(\w+)',
            re.MULTILINE
        )

    # Find all declarations
    for match in decl_pattern.finditer(content):
        kind = match.group(1)
        name = match.group(2)
        decl_start = match.start()

        # Find line number of declaration
        line_decl = content[:decl_start].count('\n')

        # Look backwards for attributes on preceding lines
        attr_line = -1
        existing_attrs = ""
        has_target = False
        line_start = line_decl

        # Check previous lines for attributes
        check_line = line_decl - 1
        while check_line >= 0:
            line_content = lines[check_line].strip()
            if line_content.startswith('@[') and line_content.endswith(']'):
                # Found an attribute line
                attr_line = check_line
                existing_attrs = line_content
                line_start = check_line
                if 'target' in line_content:
                    has_target = True
                check_line -= 1
            elif line_content == '' or line_content.startswith('--'):
                # Empty line or comment, keep looking
                check_line -= 1
            else:
                # Not an attribute, stop looking
                break

        # Extract proof text (from declaration to next declaration or end)
        # Find the end of this declaration's proof
        proof_end = len(content)
        next_match = decl_pattern.search(content, match.end())
        if next_match:
            proof_end = next_match.start()

        proof_text = content[match.start():proof_end]

        declarations.append(Declaration(
            name=name,
            kind=kind,
            has_target=has_target,
            line_start=line_start,
            line_decl=line_decl,
            attr_line=attr_line,
            file_path=file_path,
            proof_text=proof_text,
            existing_attrs=existing_attrs
        ))

    return declarations


def find_target_names(declarations: List[Declaration]) -> Set[str]:
    """Get the names of all declarations marked with @[target]."""
    return {d.name for d in declarations if d.has_target}


def find_dependencies(decl: Declaration, target_names: Set[str]) -> Set[str]:
    """
    Find which target names are used in a declaration's proof.

    We look for target names appearing in the proof text as word boundaries.
    """
    dependencies = set()
    for target_name in target_names:
        # Use word boundary to match exact names
        pattern = r'\b' + re.escape(target_name) + r'\b'
        if re.search(pattern, decl.proof_text):
            # Make sure it's not just the declaration itself
            if target_name != decl.name:
                dependencies.add(target_name)
    return dependencies


def propagate_targets(folder: str, dry_run: bool = False, quiet: bool = False,
                       include_defs: bool = True) -> Dict[str, List[str]]:
    """
    Main function to propagate @[target] to dependent declarations.

    Args:
        folder: Path to the folder to process
        dry_run: If True, don't modify files, just report what would change
        quiet: If True, reduce output verbosity
        include_defs: If True, include 'def' declarations

    Returns:
        Dict mapping file paths to list of declaration names that were/would be updated
    """
    lean_files = find_lean_files(folder)

    if not lean_files:
        print(f"No .lean files found in {folder}")
        return {}

    if not quiet:
        print(f"Found {len(lean_files)} Lean files in {folder}")

    # First pass: collect all declarations from all files
    all_declarations: List[Declaration] = []
    for file_path in lean_files:
        decls = extract_declarations(file_path, include_defs=include_defs)
        all_declarations.extend(decls)
        if not quiet:
            print(f"  {file_path}: {len(decls)} declarations")

    # Get all target names
    target_names = find_target_names(all_declarations)
    if not quiet:
        print(f"\nFound {len(target_names)} @[target] declarations")

    # Find non-target declarations that depend on targets
    updates: Dict[str, List[Tuple[Declaration, Set[str]]]] = {}

    for decl in all_declarations:
        if not decl.has_target:
            deps = find_dependencies(decl, target_names)
            if deps:
                if decl.file_path not in updates:
                    updates[decl.file_path] = []
                updates[decl.file_path].append((decl, deps))

    # Report findings
    total_updates = sum(len(v) for v in updates.values())
    if not quiet or total_updates > 0:
        print(f"\nFound {total_updates} declarations to update:")

    result: Dict[str, List[str]] = {}

    for file_path, decl_updates in updates.items():
        result[file_path] = []
        if not quiet:
            print(f"\n  {file_path}:")
        for decl, deps in decl_updates:
            if not quiet:
                print(f"    - {decl.kind} {decl.name} (depends on: {', '.join(sorted(deps))})")
            result[file_path].append(decl.name)

    if dry_run:
        if not quiet:
            print("\n[DRY RUN] No files modified.")
        return result

    # Second pass: modify files
    for file_path, decl_updates in updates.items():
        modify_file(file_path, decl_updates, quiet=quiet)

    if not quiet:
        print(f"\nUpdated {len(updates)} files.")
    return result


def modify_file(file_path: str, decl_updates: List[Tuple[Declaration, Set[str]]],
                quiet: bool = False):
    """
    Modify a file to add @[target] to the specified declarations.
    """
    with open(file_path, 'r') as f:
        lines = f.readlines()

    # Sort updates by line number in reverse order (so we can modify from bottom to top)
    decl_updates_sorted = sorted(decl_updates, key=lambda x: x[0].line_decl, reverse=True)

    for decl, deps in decl_updates_sorted:
        if decl.attr_line >= 0:
            # Has existing attributes, merge @[target] into them
            old_attr = lines[decl.attr_line].rstrip('\n')
            # Check if it's a simple @[...] pattern
            if old_attr.strip().startswith('@[') and old_attr.strip().endswith(']'):
                # Insert 'target, ' after '@['
                stripped = old_attr.strip()
                indent = old_attr[:len(old_attr) - len(old_attr.lstrip())]
                # Find position after '@['
                inner = stripped[2:-1]  # Content inside @[...]
                new_attr = f"{indent}@[target, {inner}]\n"
                lines[decl.attr_line] = new_attr
        else:
            # No existing attributes, add new @[target] line before declaration
            indent = lines[decl.line_decl][:len(lines[decl.line_decl]) - len(lines[decl.line_decl].lstrip())]
            new_line = f"{indent}@[target]\n"
            lines.insert(decl.line_decl, new_line)

    with open(file_path, 'w') as f:
        f.writelines(lines)

    if not quiet:
        print(f"  Modified: {file_path}")


def iterative_propagate(folder: str, dry_run: bool = False, quiet: bool = False,
                         include_defs: bool = True, max_iterations: int = 10) -> int:
    """
    Iteratively propagate @[target] until no more changes are needed.

    This handles transitive dependencies: if A depends on B, and B depends on C (target),
    first B gets marked as target, then A gets marked as target.

    Args:
        folder: Path to the folder to process
        dry_run: If True, don't modify files, just report what would change
        quiet: If True, reduce output verbosity
        include_defs: If True, include 'def' declarations
        max_iterations: Maximum number of iterations to prevent infinite loops

    Returns:
        Total number of declarations updated
    """
    total_updated = 0
    iteration = 0

    while iteration < max_iterations:
        iteration += 1
        if not quiet:
            print(f"\n{'='*60}")
            print(f"Iteration {iteration}")
            print('='*60)

        result = propagate_targets(folder, dry_run=dry_run, quiet=quiet,
                                   include_defs=include_defs)
        updates_this_round = sum(len(v) for v in result.values())

        if updates_this_round == 0:
            if not quiet:
                print(f"\nNo more updates needed after {iteration} iteration(s).")
            break

        total_updated += updates_this_round

        if dry_run:
            if not quiet:
                print(f"\n[DRY RUN] Would update {updates_this_round} declarations this iteration.")
            break  # In dry run mode, we can't iterate since files aren't modified
    else:
        print(f"\nWarning: Reached maximum iterations ({max_iterations}). "
              "There may be more dependencies to propagate.")

    return total_updated


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        print("\nError: Please provide a folder path.")
        print("Usage: python propagate_targets.py <folder_path> [--dry-run] [--quiet] [--include-defs]")
        sys.exit(1)

    folder = sys.argv[1]
    dry_run = '--dry-run' in sys.argv
    quiet = '--quiet' in sys.argv
    include_defs = '--include-defs' in sys.argv

    if not os.path.isdir(folder):
        print(f"Error: '{folder}' is not a valid directory.")
        sys.exit(1)

    if not quiet:
        print(f"Processing folder: {folder}")
        if dry_run:
            print("[DRY RUN MODE - no files will be modified]")
        if include_defs:
            print("[Including 'def' declarations]")

    total = iterative_propagate(folder, dry_run=dry_run, quiet=quiet,
                                 include_defs=include_defs)

    if not dry_run:
        print(f"\nTotal declarations updated: {total}")


if __name__ == '__main__':
    main()
