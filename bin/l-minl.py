#!/usr/bin/env python3

import z3
import sys
import time
from typing import List

subscript = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")

class PatternData():
    def __init__(self, filename):
        def parse_line(line):
            tokens = line.split()
            if len(tokens) > 3 and tokens[0] == "positive" and tokens[1] == "example" and tokens[3] == ":=":
                return [], [line.strip().split(" := ")[1].split()]
            elif len(tokens) > 2 and tokens[0] == "data" and tokens[2] == ":=":
                S_defn = line.strip().split(" := ")[1].split()
                S_defn = [c for c in S_defn if c != "|"]
                return [(tokens[1], S_defn)], []
            else:
                return [], []

        S = []
        S_defns: List[List[str]] = []
        with open(filename) as f:
            for line in f:
                a, b = parse_line(line)
                S_defns += a
                S += b

        if len(S) == 0:
            raise ValueError(f"No positive examples found in {filename}")

        S_defn = sorted(
            list(set(([str(c) for (_, sequence) in S_defns for c in sequence]))))

        O = sorted(list(set(([str(c) for sequence in S for c in sequence]))))
        for x in O:
            if x not in S_defn:
                raise ValueError(f"Unknown symbol: {x}")

        sort, Sigma = z3.EnumSort("Sigma", S_defn)
        S: List[str] = [[c for c in sequence] for sequence in S]

        self.sort = sort
        self.Sigma = dict(zip(S_defn, Sigma))
        self.S = S
        self.partitions = dict(S_defns)

    def is_var(self, x):
        return not x in self.Sigma

    def __str__(self) -> str:
        kinds = "\n\t".join(
            map(lambda p: "%s: {%s}" % (p[0], ", ".join(p[1])), self.partitions.items()))
        datas = "\n\t".join(map(lambda s: "⋅".join(s), self.S))
        return f"Sigma:\t{kinds}\n\nData:\t{datas}"


def remove_duplicates(seq):
    seen = set()
    seen_add = seen.add
    return [x for x in seq if not (x in seen or seen_add(x))]


def replace(seq, old, new):
    return [new if x == old else x for x in seq]


def learn_pattern(data: PatternData):
    S = data.S
    Sigma = data.Sigma
    sort = data.sort
    is_var = data.is_var

    w = [s for s in S if all(map(lambda x: len(x) >= len(s), S))][0]
    x = [f"Y{i}" for i in range(len(w))]
    a = w
    p = [x]
    m = len(p[0])

    def member(s, q: List[str]):
        solver = z3.Solver()

        vars = {}
        for x in q:
            if is_var(x) and x not in vars:
                x_var = z3.Const(x, z3.SeqSort(sort))
                vars[x] = x_var
                solver.add(z3.Length(x_var) > 0)

        pattern = z3.Concat(
            [vars[x] if x in vars else z3.Unit(Sigma[x]) for x in q])
        target = z3.Concat([z3.Unit(Sigma[x]) for x in s])
        solver.add(pattern == target)

        return solver.check() == z3.sat

    def subset(S, q: List[str]):
        return all(member(s, q) for s in S)

    for i in range(m):
        q = replace(p[i], x[i], a[i])
        j = i + 1
        while not subset(S, q) and j < m:
            q = replace(p[i], x[i], x[j])
            j += 1
        if subset(S, q):
            p.append(q)
        else:
            p.append(p[i])

    output = p[-1]
    return output


def find_singles(data: PatternData, pattern):
    S = data.S
    Sigma = data.Sigma
    sort = data.sort
    is_var = data.is_var

    ys = remove_duplicates([y for y in pattern if is_var(y)])

    def check_single(s, q, candidate):
        solver = z3.Solver()

        vars = {}
        for x in q:
            if is_var(x) and x not in vars:
                x_var = z3.Const(x, z3.SeqSort(sort))
                vars[x] = x_var
                if x == candidate:
                    solver.add(z3.Length(x_var) > 1)
                else:
                    solver.add(z3.Length(x_var) > 0)

        pattern = z3.Concat(
            [vars[x] if x in vars else z3.Unit(Sigma[x]) for x in q])
        target = z3.Concat([z3.Unit(Sigma[x]) for x in s])
        solver.add(pattern == target)

        answer = solver.check()
        return answer == z3.unsat

    singles = []
    for y in ys:
        if y not in singles and all(check_single(s, pattern, y) for s in S):
            singles.append(y)

    return singles


def find_restricted(data: PatternData, pattern):
    S = data.S
    Sigma = data.Sigma
    sort = data.sort
    is_var = data.is_var
    subsets = data.partitions

    ys = remove_duplicates([y for y in pattern if is_var(y)])

    def check_restricted(s, q, y, not_in):
        solver = z3.Solver()

        vars = {}
        for x in q:
            if is_var(x) and x not in vars:
                x_var = z3.Const(x, z3.SeqSort(sort))
                vars[x] = x_var
                solver.add(z3.Length(x_var) > 0)
                if x == y:
                    # if it is not possible to contain something out of the subset, then it is restricted.
                    solver.add(
                        z3.Or([z3.Contains(x_var, z3.Unit(Sigma[z])) for z in not_in]))

        pattern = z3.Concat(
            [vars[x] if x in vars else z3.Unit(Sigma[x]) for x in q])
        target = z3.Concat([z3.Unit(Sigma[x]) for x in s])
        solver.add(pattern == target)

        answer = solver.check()
        return answer == z3.unsat

    restricted_vars = []
    restricted_subs = []
    for y in ys:
        for (name, subset) in subsets.items():
            if y not in restricted_vars:
                not_in = [x for x in Sigma.keys() if x not in subset]
                if all(check_restricted(s, pattern, y, not_in) for s in S):
                    restricted_vars.append(y)
                    restricted_subs.append(name)

    return dict(zip(restricted_vars, restricted_subs))


if __name__ == "__main__":
    """
    Input argument is a path to a file containing a set of sequences.
    """
    divider = "*"*30
    data = PatternData(sys.argv[1])
    input = f"{divider} Input  {divider}\n\n{data}"
    input = input.translate(subscript)
    print(input)

    times = [0, 0, 0]
    times[0] = time.time()
    pattern = learn_pattern(data)
    times[0] = time.time() - times[0]

    def normalize(p):
        output = p
        ys = remove_duplicates([y for y in output if data.is_var(y)])
        xs = [f"x{i}" for i in range(len(ys))]
        for (x, y) in zip(xs, ys):
            output = replace(output, y, x)
        return output

    pattern = normalize(pattern)

    times[1] = time.time()
    singles = find_singles(data, pattern)
    times[1] = time.time() - times[1]
    times[2] = time.time()
    restricted = find_restricted(data, pattern)
    times[2] = time.time() - times[2]

    annotation = []
    visited = set()
    for x in pattern:
        if data.is_var(x) and x not in visited:
            visited.add(x)
            single = x in singles
            kind = restricted[x] if x in restricted else f"{data.sort}"
            annotation.append(f"{x} ∈ {kind}" if single else f"{x} ∈ {kind}⁺")

    pattern = "⋅".join(pattern)
    annotation = " ∧ ".join(annotation)

    output = f"\n{divider} Output {divider}\n\nPat.:\t{pattern} [{annotation}]"
    output = output.translate(subscript)
    print(output)
    
    stats = f"\nTime:\ttotal:  {sum(times)}s\n\tl-minl: {times[0]}s\n\tlength: {times[1]}s\n\tmember: {times[2]}s\n"
    print(stats)
