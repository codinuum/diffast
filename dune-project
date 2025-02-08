(lang dune 3.17)

(name diffast)

(generate_opam_files true)

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

(documentation https://url/to/documentation)

(package
 (name diffast)
 (synopsis "Diff/AST: A fine-grained source code differencing tool")
 (description "Diff/AST: A fine-grained source code differencing tool")
 (allow_empty)
 (depends
   ocaml
   diffast-misc
   diffast-core
   diffast-etc
   diffast-api
   diffast-cli
   diffast-git
   diffast-git-cli

   diffast-langs-common
   ;diffast-langs-astml
   diffast-langs-cpp
   diffast-langs-cpp-parsing
   diffast-langs-fortran
   diffast-langs-fortran-parsing
   diffast-langs-java
   diffast-langs-java-parsing
   diffast-langs-python
   diffast-langs-python-parsing
   diffast-langs-verilog
   diffast-langs-verilog-parsing
 )
)
