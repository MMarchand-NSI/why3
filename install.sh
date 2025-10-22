sudo apt update
sudo apt install -y opam git m4 pkg-config
opam init -y --disable-sandboxing
eval $(opam env)
opam switch create 5.2.1  # (ou une version OCaml récente proposée)
eval $(opam env)

# Why3 + IDE
opam install -y why3 why3-ide

# Proveurs (au minimum Alt-Ergo, Z3, CVC5)
opam install -y alt-ergo
sudo apt install -y z3 cvc5  # (ou via opam: opam install z3 cvc5)

# Détection automatique
why3 config detect
