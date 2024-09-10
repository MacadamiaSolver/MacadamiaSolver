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
   (alcotest :with-test)
   (ocamlformat
    (and
     (= 0.26.2)
     :dev)))
 (tags
  (solver theorem)))

