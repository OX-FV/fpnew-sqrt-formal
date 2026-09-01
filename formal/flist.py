'''
Copyright 2026 University of Oxford.
Licensed under the Apache License, Version 2.0 (see LICENSE for details).
Original Author: Louis-Emile Ploix
SPDX-License-Identifier: Apache-2.0



This is a utility program for handling filelists, such as formal.flist. It
1. Reads and parses filelists
2. Flattens them (filelists can contain references to other filelists)
3. Does environment variable substitution on paths and path resolution
4. Prints the new flist to stdout.

It can also (as fusesoc does, but without core files) produce a mirror
copy of everything the filelist references.
'''

from dataclasses import dataclass
from typing import Union
import os, sys
import re
import argparse
import shutil
import pathlib

@dataclass(frozen=True)
class Blank:
    pass

@dataclass(frozen=True)
class Comment:
    comment: str

@dataclass(frozen=True)
class File:
    path: str

@dataclass(frozen=True)
class IncDir:
    path: str

@dataclass(frozen=True)
class Recurse:
    flist_path: str


FlistEntry = Comment | Blank | File | IncDir | Recurse
FlatFlistEntry = Comment | Blank | File | IncDir

def envsubst(s: str) -> str:
    def lookup(m: re.Match) -> str:
        n = m[1]
        e = os.getenv(n)
        if e is None:
            print(f"Required environment variable '{n}' not found", file=sys.stderr)
            exit(1)
        return e
    return re.sub(r"\$\{([a-zA-Z0-9_]+)\}", lookup, s)

def parse_flist(src: str) -> list[FlistEntry]:
    entries = []
    for line in src.split("\n"):
        line = line.strip()
        line = line.split("//", maxsplit=1)
        if len(line) == 2 and line[0].strip() == "":
            entries.append(Comment(line[1]))
            continue
        # drop comments that only take part of the line, but keep full line comments
        line = line[0].strip()

        if line == "":
            entries.append(Blank())
        elif line.startswith("-F "):
            entries.append(Recurse(envsubst(line[2:].strip())))
        elif line.startswith("+incdir+"):
            entries.append(IncDir(envsubst(line[8:].strip())))
        else: # fallback to a regular file
            entries.append(File(envsubst(line)))
    return entries

def get_flat_flist(path: str) -> list[FlatFlistEntry]:
    with open(path, "r") as f:
        txt = f.read()
    reclist = parse_flist(txt)
    flatlist = []
    for entry in reclist:
        match entry:
            case Recurse(flist_path=path):
                flatlist.extend(get_flat_flist(path))
            case _:
                flatlist.append(entry)
    return flatlist

def abs_paths(flat: list[FlatFlistEntry]) -> list[FlatFlistEntry]:
    mapped = []
    for entry in flat:
        match entry:
            case IncDir(path=path):
                mapped.append(IncDir(os.path.abspath(path)))
            case File(path=path):
                mapped.append(File(os.path.abspath(path)))
            case _:
                mapped.append(entry)
    return mapped

def find_common_base(flat: list[FlatFlistEntry]) -> str:
    paths = []
    for entry in flat:
        match entry:
            case IncDir(path=path) | File(path=path):
                paths.append(path)
            case _: pass
    return os.path.commonprefix(paths)

def copy_files(flat: list[FlatFlistEntry], prefix: str, new_base: str) -> list[FlatFlistEntry]:
    mapped = []
    for entry in flat:
        match entry:
            case IncDir(path=path):
                assert path.startswith(prefix)
                new = os.path.join(new_base, path[len(prefix):])
                os.makedirs(new, exist_ok=True)
                shutil.copytree(path, new, dirs_exist_ok=True)
                mapped.append(IncDir(new))
            case File(path=path):
                assert path.startswith(prefix)
                new = os.path.join(new_base, path[len(prefix):])
                os.makedirs(os.path.dirname(new), exist_ok=True)
                shutil.copyfile(path, new)
                mapped.append(File(new))
            case _:
                mapped.append(entry)
    return mapped

parser = argparse.ArgumentParser(prog="flist.py", description="""
                                 Reads a filelist, parses it, flattens it and does environment variable
                                 substitution on paths, path expansion, and prints the result to stdout.
                                 """)
parser.add_argument("flist", help="Root filelist")
parser.add_argument("--copy", help="Make a local copy of the file tree and output a mapped filelist. Will find the common prefix between paths to trim, but will otherwise mirror directory structure")
args = parser.parse_args()

l = get_flat_flist(args.flist)
l = abs_paths(l)

if args.copy != None:
    new_base = os.path.abspath(args.copy)
    shutil.rmtree(new_base, ignore_errors=True)
    base = find_common_base(l)
    l = copy_files(l, base, new_base)

for entry in l:
    match entry:
        case Blank():
            print()
        case Comment(comment=c):
            print("//" + c)
        case IncDir(path=path):
            print("+incdir+" + path)
        case File(path=path):
            print(path)
