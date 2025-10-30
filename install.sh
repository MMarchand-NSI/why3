# Why3 + IDE
opam install -y why3 why3-ide

# Proveurs (au minimum Alt-Ergo, Z3, CVC5)
opam install -y alt-ergo z3 cvc5

# Détection automatique
why3 config detect
