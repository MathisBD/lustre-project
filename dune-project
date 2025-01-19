(lang dune 3.17)

(using menhir 3.0)

(name lustre-project)

(generate_opam_files true)

(package
 (name lustre-project)
 (license MIT)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (homepage "https://github.com/MathisBD/lustre-project")
 (bug_reports "https://github.com/MathisBD/lustre-project/issues")
 (synopsis
  "Project for course 'Modèles et langages pour la programmation des systèmes réactifs'")
 (depends ppx_deriving menhir))
