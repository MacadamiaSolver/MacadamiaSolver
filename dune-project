(lang dune 3.16)

(name MacadamiaSolver)

(generate_opam_files true)

(source
 (github MacadamiaSolver/MacadamiaSolver))

(authors "Georgiy Belyanin, Timofey Frolov, Ignat Sergeev")

(maintainers "Georgiy Belyanin, Timofey Frolov, Ignat Sergeev")

(license LICENSE)

(package
 (name MacadamiaSolver)
 (synopsis "Theorem Solver")
 (depends
  ocaml
  dune
  angstrom
  bitv
  ppx_deriving
  ppx_variants_conv
  (ppx_expect :with-test)
  (ppx_inline_test :with-test)
  (ocamlformat :dev))
 (tags
  (solver theorem)))

