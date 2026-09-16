#!/usr/bin/env python3
"""Index pinned official source syntax, not C++/Python correctness.

No source program is executed. Requires tree-sitter==0.25.2,
tree-sitter-cpp==0.23.4 and PyYAML==6.0.3. --check compares the *entire*
regenerated inventory, so omitted or modified occurrences fail verification.
Git blobs are independently hashed before parsing. Gitlinks are explicit
external boundaries and are not recursively claimed as inspected source.
"""
from __future__ import annotations
import argparse
import ast
import hashlib
import importlib.metadata
import json
import gzip
from pathlib import Path
import re
import sys
import subprocess

PIN = "7960a42750f3407ea9eb2c3333d4c2a7961f6df4"
VERSIONS = {"tree-sitter": "0.25.2", "tree-sitter-cpp": "0.23.4", "PyYAML": "6.0.3"}
CPP_KINDS = {"function_definition", "function_declarator", "lambda_expression",
             "field_declaration", "declaration", "optional_parameter_declaration",
             "preproc_def", "preproc_function_def"}


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def parent_for(path: str) -> str:
    if path.startswith("conf/common/optimizer"):
        return "NN-OPTIMIZER"
    if path.startswith("conf/"):
        return "EVAL-REPRO"
    if "models.py" in path:
        return "NN-VALUE"
    if "selfplay.py" in path:
        return "NN-LOSS"
    if "prioritized_replay" in path:
        return "NN-REPLAY"
    if "/rela/" in path or "real_net" in path or "net_interface" in path:
        return "NN-CONCURRENT"
    if path.endswith(("liars_dice.cc", "liars_dice.h", "liars_dice_test.cc")):
        return "GAME-LIARS"
    if "subgame_solving" in path:
        return "CFR-SCHEDULE"
    if "recursive_solving" in path:
        return "ALG-ONE"
    if "eval" in path or "stats" in path or "benchmark" in path:
        return "EVAL-METRIC"
    return "EXEC-REFINE"


def compact(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()[:150]


def python_rows(text: str) -> list[list]:
    root = ast.parse(text)
    rows = []
    def add(node: ast.AST, kind: str, name: str) -> None:
        rows.append([node.lineno, node.col_offset, node.end_lineno, kind, compact(name)])
    def walk(node: ast.AST, scope: str = "") -> None:
        child_scope = scope
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            name = scope + node.name
            kind = "py-class" if isinstance(node, ast.ClassDef) else "py-function"
            add(node, kind, name)
            child_scope = name + "."
            if not isinstance(node, ast.ClassDef):
                params = node.args.posonlyargs + node.args.args
                for arg, val in zip(params[-len(node.args.defaults):], node.args.defaults):
                    add(val, "py-default", name + ":" + arg.arg + "=" + ast.unparse(val))
                for arg, val in zip(node.args.kwonlyargs, node.args.kw_defaults):
                    if val is not None:
                        add(val, "py-default", name + ":" + arg.arg + "=" + ast.unparse(val))
        elif isinstance(node, ast.Lambda):
            add(node, "py-lambda", scope + "<lambda>")
        elif isinstance(node, ast.Call):
            func = ast.unparse(node.func)
            if func.endswith((".get", ".add_argument", ".set_defaults")):
                add(node, "py-option-read", ast.unparse(node))
            if func in {"getattr", "setattr", "hasattr"}:
                add(node, "py-dynamic-attribute", ast.unparse(node))
            for kw in node.keywords:
                add(kw.value, "py-keyword", func + ":" + str(kw.arg) + "=" + ast.unparse(kw.value))
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            add(node, "py-binding", ast.unparse(node).split("\n", 1)[0])
        for child in ast.iter_child_nodes(node):
            walk(child, child_scope)
    walk(root)
    return sorted(rows)


def cpp_rows(raw: bytes, parser) -> list[list]:
    root = parser.parse(raw).root_node
    if root.has_error:
        raise ValueError("C++ parse contains ERROR or missing nodes")
    rows = []
    def walk(node) -> None:
        if node.type in CPP_KINDS:
            label = node.child_by_field_name("declarator")
            if label is None:
                label = node
            text = raw[label.start_byte:label.end_byte].decode("utf-8")
            rows.append([node.start_point.row + 1, node.start_point.column,
                         node.end_point.row + 1, "cpp-" + node.type, compact(text)])
        for child in node.children:
            walk(child)
    walk(root)
    return sorted(rows)


def yaml_rows(text: str, yaml) -> list[list]:
    rows = []
    def walk(node, path: str, ancestors: set[int]) -> None:
        if id(node) in ancestors:
            raise ValueError("recursive YAML alias is not an enumerable configuration")
        ancestors = ancestors | {id(node)}
        if isinstance(node, yaml.ScalarNode):
            rows.append([node.start_mark.line + 1, node.start_mark.column,
                         node.end_mark.line + 1, "yaml-value", compact(path + "=" + node.value)])
        elif isinstance(node, yaml.MappingNode):
            keys = set()
            for key, value in node.value:
                if not isinstance(key, yaml.ScalarNode) or key.value in keys:
                    raise ValueError("non-scalar or duplicate YAML key")
                keys.add(key.value)
                walk(value, path + "." + key.value, ancestors)
        elif isinstance(node, yaml.SequenceNode):
            for i, value in enumerate(node.value):
                walk(value, path + f"[{i}]", ancestors)
    for i, node in enumerate(yaml.compose_all(text)):
        if node is not None:
            walk(node, str(i), set())
    return sorted(rows)


def inventory(source: Path, tree: Path) -> dict:
    if (source / ".git").exists():
        head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        actual_tree = subprocess.check_output(["git", "-C", str(source), "ls-tree", "-rl", "HEAD"])
        if head != PIN or actual_tree != tree.read_bytes():
            raise ValueError("checkout commit or complete tracked tree differs")
    for name, version in VERSIONS.items():
        if importlib.metadata.version(name) != version:
            raise ValueError(f"pin mismatch: {name} must equal {version}")
    from tree_sitter import Language, Parser
    import tree_sitter_cpp
    import yaml
    parser = Parser(Language(tree_sitter_cpp.language()))
    result = {"schema": 1, "commit": PIN, "tree_sha256": digest(tree.read_bytes()),
              "parser_versions": VERSIONS, "columns": ["line", "column", "end_line", "kind", "label"],
              "files": []}
    seen = set()
    for line in tree.read_text().splitlines():
        meta, path = line.split("\t", 1)
        mode, kind, sha, size = meta.split()
        if path in seen or Path(path).is_absolute() or ".." in Path(path).parts:
            raise ValueError(f"duplicate/unsafe tree path {path}")
        seen.add(path)
        entry = {"path": path, "mode": mode, "git_sha": sha, "parent": parent_for(path)}
        if kind == "commit":
            if mode != "160000":
                raise ValueError("unexpected gitlink mode")
            entry.update({"kind": "gitlink", "rows": []})
            result["files"].append(entry)
            continue
        raw = (source / path).read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if actual != sha or len(raw) != int(size):
            raise ValueError(f"official blob does not match pin: {path}")
        text = raw.decode("utf-8")
        entry.update({"kind": "blob", "sha256": digest(raw), "lines": len(text.splitlines())})
        if path.endswith(".py"):
            rows = python_rows(text)
        elif path.endswith((".cc", ".h")):
            rows = cpp_rows(raw, parser)
        elif path.endswith((".yaml", ".yml")):
            rows = yaml_rows(text, yaml)
        else:
            # Explicit operational/configuration lines, and prose/license context.
            rows = [[n, 0, n, "context-line" if path.endswith(".md") or path == "LICENSE"
                     else "build-setting", compact(s)] for n, s in enumerate(text.splitlines(), 1)
                    if s.strip() and not s.lstrip().startswith("#")]
        if len({tuple(row) for row in rows}) != len(rows):
            raise ValueError(f"duplicate occurrence: {path}")
        entry["rows"] = rows
        result["files"].append(entry)
    return result


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--tree", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--check", action="store_true")
    a = p.parse_args()
    try:
        data = inventory(a.source, a.tree)
        if a.check:
            raw = a.output.read_bytes()
            if a.output.suffix == ".gz":
                raw = gzip.decompress(raw)
            if json.loads(raw) != data:
                raise ValueError("official inventory differs: regenerate and review the diff")
        else:
            raw = (json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n").encode()
            a.output.write_bytes(gzip.compress(raw, mtime=0) if a.output.suffix == ".gz" else raw)
        print(f"OFFICIAL_INVENTORY_PASS files={len(data['files'])} occurrences="
              f"{sum(len(f['rows']) for f in data['files'])}; syntax/provenance only")
    except (OSError, ValueError, UnicodeError, SyntaxError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
