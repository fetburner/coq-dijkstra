(lang dune 2.5)
(using coq 0.2)
(name coq-dijkstra)

(generate_opam_files true)

(license MIT)
(authors "Masayuki Mizuno <mizuno@wantedly.com>")
(maintainers "Masayuki Mizuno <mizuno@wantedly.com>")
(source (github fetburner/coq-dijkstra))

(package
  (name coq-dijkstra)
  (synopsis "A Verified Implementation of Dijkstra's Algorithm")
  (depends
    (coq (>= 8.8))
    (coq-mathcomp-ssreflect (>= 1.11))))

