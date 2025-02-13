(lang dune 3.17)

(using dune_site 0.1)
(using menhir 3.0)

(name diffast)

(generate_opam_files true)
(opam_file_location inside_opam_directory)

(source
 (github codinuum/diffast))

(authors
  "Codinuum <codinuum@me.com>"
  "Masatomo Hashimoto <m.hashimoto@stair.center>"
)

(maintainers
  "Codinuum <codinuum@me.com>"
  "Masatomo Hashimoto <m.hashimoto@stair.center>"
)

(license Apache-2.0)

(documentation https://github.com/codinuum/diffast/README.md)

(package
 (name diffast)
 (synopsis "Diff/AST: A fine-grained source code differencing tool")
 (description "Diff/AST: A fine-grained source code differencing tool")
 (allow_empty)
 (depends
   (ocaml (>= 4.14))
   (diffast-misc (= :version))
   (diffast-core (= :version))
   (diffast-etc (= :version))
   (diffast-api (= :version))
   (diffast-cli (= :version))
   (diffast-git (= :version))
   (diffast-git-cli (= :version))
   (diffast-langs-common (= :version))
   (diffast-langs-cpp-parsing (= :version))
   (diffast-langs-fortran-parsing (= :version))
   (diffast-langs-java-parsing (= :version))
   (diffast-langs-python-parsing (= :version))
   (diffast-langs-verilog-parsing (= :version))
   ;(diffast-langs-astml (= :version))
   (diffast-langs-cpp (= :version))
   (diffast-langs-fortran (= :version))
   (diffast-langs-java (= :version))
   (diffast-langs-python (= :version))
   (diffast-langs-verilog (= :version))
 )
)

(package
 (name diffast-misc)
 (synopsis "Miscellaneous functions for Diff/AST")
 (description "Miscellaneous functions for Diff/AST")
 (depends
   (ocaml (>= 4.14))
   dune
   (base64 (>= 3.0.0))
   bytesrw
   cryptokit
   markup
   (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-core)
 (sites (lib lang_specs) (lib langs))
 (synopsis "Core of Diff/AST")
 (description "Core of Diff/AST")
 (depends
  (ocaml (>= 4.14))
  dune
  dune-site
  camlp-streams
  uuidm
  csv
  base64
  sedlex
  menhir
  (diffast-misc (= :version))
  (vlt (>= 0.2.4))
 )
 (tags
  ("abstract syntax tree" differencing))
)

(package
 (name diffast-etc)
 (synopsis "Diff/AST etc files")
 (description "Diff/AST etc files")
 (depends
   (ocaml (>= 4.14))
   dune
 )
)

(package
 (name diffast-api)
 (synopsis "Diff/AST API")
 (description "Diff/AST API")
 (depends
  (ocaml (>= 4.14))
  dune
  (diffast-misc (= :version))
  (diffast-core (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-cli)
 (synopsis "Diff/AST command line")
 (description "Diff/AST command line")
 (depends
  (ocaml (>= 4.14))
  dune
  (diffast-core (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-git)
 (synopsis "Git functions for Diff/AST")
 (description "Git functions for Diff/AST API")
 (depends
  (ocaml (>= 4.14))
  dune
  git-unix
  (diffast-misc (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-git-cli)
 (synopsis "Git-Diff/AST command line")
 (description "Git-Diff/AST command line")
 (depends
  (ocaml (>= 4.14))
  dune
  (diffast-core (= :version))
  (diffast-api (= :version))
  (diffast-git (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-common)
 (synopsis "Common functions for parsers of Diff/AST")
 (description "Common functions for parsers of Diff/AST")
 (depends
  (ocaml (>= 4.14))
  dune
  sedlex
  mehirLib
  (diffast-misc (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-cpp-parsing)
 (synopsis "C++/C parser for Diff/AST")
 (description "C++/C parser for Diff/AST")
 (depends
  (ocaml (>= 4.14))
  camlp-streams
  sedlex
  menhir
  (diffast-langs-common (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-fortran-parsing)
 (synopsis "Fortran parser for Diff/AST")
 (description "Fortran parser for Diff/AST")
 (depends
  (ocaml (>= 4.14))
  camlp-streams
  sedlex
  menhir
  (diffast-langs-common (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-java-parsing)
 (synopsis "Java parser for Diff/AST")
 (description "Java parser for Diff/AST")
 (depends
  (ocaml (>= 4.14))
  camlp-streams
  sedlex
  menhir
  (diffast-langs-common (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-python-parsing)
 (synopsis "Python parser for Diff/AST")
 (description "Python parser for Diff/AST")
 (depends
  (ocaml (>= 4.14))
  camlp-streams
  sedlex
  menhir
  (diffast-langs-common (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-verilog-parsing)
 (synopsis "Verilog parser for Diff/AST")
 (description "Verilog parser for Diff/AST")
 (depends
  (ocaml (>= 4.14))
  camlp-streams
  sedlex
  menhir
  (diffast-langs-common (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-astml)
 (synopsis "ASTML parser for Diff/AST")
 (description "ASTML parser for Diff/AST")
)

(package
 (name diffast-langs-cpp)
 (synopsis "C++/C parser plugin for Diff/AST")
 (description "C++/C parser plugin for Diff/AST")
 (depends
  dune-site
  (diffast-cpp-parsing (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-fortran)
 (synopsis "Fortran parser plugin for Diff/AST")
 (description "Fortran parser plugin for Diff/AST")
 (depends
  dune-site
  (diffast-fortran-parsing (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-java)
 (synopsis "Java parser plugin for Diff/AST")
 (description "Java parser plugin for Diff/AST")
 (depends
  dune-site
  (diffast-java-parsing (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-python)
 (synopsis "Python parser plugin for Diff/AST")
 (description "Python parser plugin for Diff/AST")
 (depends
  dune-site
  (diffast-python-parsing (= :version))
  (vlt (>= 0.2.4))
 )
)

(package
 (name diffast-langs-verilog)
 (synopsis "Verilog parser plugin for Diff/AST")
 (description "Verilog parser plugin for Diff/AST")
 (depends
  dune-site
  (diffast-verilog-parsing (= :version))
  (vlt (>= 0.2.4))
 )
)

;

(package
  (name diffast-langs-cpp-parsing-cli)
  (synopsis "C/C++ parser CLI")
  (depends
   dynlink
   threads
   (diffast-langs-cpp-parsing (= :version))
  )
)

(package
  (name diffast-langs-fortran-parsing-cli)
  (synopsis "Fortran parser CLI")
  (depends
   dynlink
   threads
   (diffast-langs-fortran-parsing (= :version))
  )
)

(package
  (name diffast-langs-java-parsing-cli)
  (synopsis "Java parser CLI")
  (depends
   dynlink
   threads
   (diffast-langs-java-parsing (= :version))
  )
)

(package
  (name diffast-langs-python-parsing-cli)
  (synopsis "Python parser CLI")
  (depends
   dynlink
   threads
   (diffast-langs-python-parsing (= :version))
  )
)

(package
  (name diffast-langs-verilog-parsing-cli)
  (synopsis "Verilog parser CLI")
  (depends
   dynlink
   threads
   (diffast-langs-verilog-parsing (= :version))
  )
)
