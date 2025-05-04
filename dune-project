(lang dune 3.16)
(using coq 0.8)
(generate_opam_files true)
(license AGPL-3.0-only)
(authors
 "Frédéric Dabrowski <frederic.dabrowski@univ-orleans.fr>")
(maintainers
 "Frédéric Dabrowski <frederic.dabrowski@univ-orleans.fr>")
(source (github DabrowskiFr/CategoryTheoryCoq))
(package 
 (name CRocq)
 (synopsis "Category Theory")
 (description "A Coq library for category theory")
 (depends (coq (>= 8.20.0))))