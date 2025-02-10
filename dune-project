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
   diffast-misc
   diffast-core
   diffast-etc
   diffast-api
   diffast-cli
   diffast-git
   diffast-git-cli

   diffast-langs-common
   diffast-langs-cpp-parsing
   diffast-langs-fortran-parsing
   diffast-langs-java-parsing
   diffast-langs-python-parsing
   diffast-langs-verilog-parsing

   ;diffast-langs-astml
   diffast-langs-cpp
   diffast-langs-fortran
   diffast-langs-java
   diffast-langs-python
   diffast-langs-verilog
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
   (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-misc
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-misc
  diffast-core
  (vlt (or (<> :platform windows) (>= 0.2.4)))
 )
)

(package
 (name diffast-cli)
 (synopsis "Diff/AST command line")
 (description "Diff/AST command line")
 (depends
  (ocaml (>= 4.14))
  dune
  diffast-core
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-misc
  (vlt (or (<> :platform windows) (>= 0.2.4)))
 )
)

(package
 (name diffast-git-cli)
 (synopsis "Git-Diff/AST command line")
 (description "Git-Diff/AST command line")
 (depends
  (ocaml (>= 4.14))
  dune
  diffast-core
  diffast-api
  diffast-git
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-misc
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-langs-common
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-langs-common
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-langs-common
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-langs-common
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-langs-common
  (vlt (or (<> :platform windows) (>= 0.2.4)))
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
  diffast-cpp-parsing
  (vlt (or (<> :platform windows) (>= 0.2.4)))
 )
)

(package
 (name diffast-langs-fortran)
 (synopsis "Fortran parser plugin for Diff/AST")
 (description "Fortran parser plugin for Diff/AST")
 (depends
  dune-site
  diffast-fortran-parsing
  (vlt (or (<> :platform windows) (>= 0.2.4)))
 )
)

(package
 (name diffast-langs-java)
 (synopsis "Java parser plugin for Diff/AST")
 (description "Java parser plugin for Diff/AST")
 (depends
  dune-site
  diffast-java-parsing
  (vlt (or (<> :platform windows) (>= 0.2.4)))
 )
)

(package
 (name diffast-langs-python)
 (synopsis "Python parser plugin for Diff/AST")
 (description "Python parser plugin for Diff/AST")
 (depends
  dune-site
  diffast-python-parsing
  (vlt (or (<> :platform windows) (>= 0.2.4)))
 )
)

(package
 (name diffast-langs-verilog)
 (synopsis "Verilog parser plugin for Diff/AST")
 (description "Verilog parser plugin for Diff/AST")
 (depends
  dune-site
  diffast-verilog-parsing
  (vlt (or (<> :platform windows) (>= 0.2.4)))
 )
)

;

(package
  (name diffast-langs-cpp-parsing-cli)
  (synopsis "C/C++ parser CLI")
  (depends
   dynlink threads diffast-langs-cpp-parsing
  )
)

(package
  (name diffast-langs-fortran-parsing-cli)
  (synopsis "Fortran parser CLI")
  (depends
   dynlink threads diffast-langs-fortran-parsing
  )
)

(package
  (name diffast-langs-java-parsing-cli)
  (synopsis "Java parser CLI")
  (depends
   dynlink threads diffast-langs-java-parsing
  )
)

(package
  (name diffast-langs-python-parsing-cli)
  (synopsis "Python parser CLI")
  (depends
   dynlink threads diffast-langs-python-parsing
  )
)

(package
  (name diffast-langs-verilog-parsing-cli)
  (synopsis "Verilog parser CLI")
  (depends
   dynlink threads diffast-langs-verilog-parsing
  )
)
