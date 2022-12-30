(lang dune 2.8)

(name genk)

(generate_opam_files true)

(source
 (github plankp/RKM))

(authors "Paul Teng")

(maintainers "plankp@outlook.com")

(license LICENSE)

(documentation https://github.com/plankp/RKM/blob/main/README.md)

(package
 (name genk)
 (synopsis "Just yet another programming language")
 (depends
  (ocaml (>= 4.08.0))
  (dune (>= 2.8.0))
  (zarith (>= 1.10))))
