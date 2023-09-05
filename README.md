# UPVerifier
Unbounded Verification of P(-like) Programs.

## Installation
```sh
# Get OCaml Setup
brew install opam
opam init
opam switch 4.12.0
opam install dune

# Install dependencies
make deps

# Install smpi and smpc
make install
```

## Usage

### Interpreter/Fuzzer (SMPI)
```sh
# Running the interpreter:
smpi examples/set.smp examples/shared.smp
# Should print:
# true
# false
# true
```

### Compiler (SMPC)
```sh
# Running the compiler and piping into an SMT solver like z3:
smpc examples/set.smp examples/shared.smp | z3 -in
# Should print:
# sat
# (((select arr A) true))
# (((select arr B) false))
# (((select arr C) true))
```

### Learner (l-minl)
```sh
# Running the l-minl Python script like:
# (assuming you have z3 python bindings installed) 
python3 bin/l-minl.py examples/client_server_ae_db_indexes.data
# Should print something like:
# ****************************** Input  ******************************

# Sigma:  C: {C₁, C₂}
#         S: {S₁, S₂}
#         D: {D₁, D₂}

# Data:   C₁⋅S₁⋅D₁⋅S₁⋅C₁
#         C₂⋅S₂⋅D₂⋅S₂⋅C₂
#         C₂⋅S₁⋅D₂⋅S₁⋅C₂

# ****************************** Output ******************************

# Pat.:   x₀⋅x₁⋅x₂⋅x₁⋅x₀ [x₀ ∈ C ∧ x₁ ∈ S ∧ x₂ ∈ D]

# Time:   total:  1.0957388877868652s
#         l-minl: 0.5688109397888184s
#         length: 0.16820192337036133s
#         member: 0.35872602462768555s
```