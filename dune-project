(lang dune 2.8)
(name rkm)
(version c642c34-dirty)

(generate_opam_files true)

(source (github plankp/RKM))
(authors "Paul Teng")
(maintainers "plankp@outlook.com")

(package
 (name rkm)
 (synopsis "Just yet another programming language")
 (depends
  (dune (>= 2.8.0))
  (ocaml (>= 4.04.0))
  (zarith (>= 1.10))))
