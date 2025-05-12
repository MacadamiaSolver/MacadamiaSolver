(lang dune 3.16)

(name Chrobelias)

(generate_opam_files true)

(source
 (github Chrobelias/Chrobelias))

(authors "Georgiy Belyanin, Timofey Frolov, Ignat Sergeev")

(maintainers "Georgiy Belyanin, Timofey Frolov, Ignat Sergeev")

(license LICENSE)

(package
 (name Chrobelias)
 (synopsis "Chrobak existential linear integer arithmetic solver")
 (depends
  ocaml
  dune
  angstrom
  bitv
  ppx_regexp
  ppx_deriving
  ppx_variants_conv
  (ppx_expect :with-test)
  (ppx_inline_test :with-test)
  (ocamlformat :dev))
 (tags
  (solver theorem)))

