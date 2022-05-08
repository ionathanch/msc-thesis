# The Future Home of Jonathan's Master's Thesis

## Outline (outdated)

1. Introduction
   1. Something whimsical
   2. Dependent types
   3. Sized types
   4. Syntactic model
   4. Outline (typographical notes might go here)
2. Sized CCω
   1. CCω
      1. Universes and cumulativity
      2. Untyped convertibility, η-conversion, congruence, transitivity
   2. Sized types
      1. Basics
      3. Higher-rank sizes
      2. [Inflationary/bounded sizes](https://ionathan.ch/2021/08/26/using-sized-types.html#3-inflationary-sized-types)
   3. Naturals and W types
   4. (Future work?) Inductives, streams, and coinductives
3. Syntactic Model
   1. Extensional CIC (Oury's CC<sub>E</sub> + inductives)
      <br/> (if CCω is separate from Sized CCω, CIC<sub>E</sub> could go with it)
   2. Recipe for a syntactic model and trivial translations
   3. Sizes as ordinals in type theory
      1. Successor and limit
      2. Ordering of sizes
      3. Accessibility of sizes wrt order
      4. Well-orderedness of sizes (induction principle)
   4. Translation of naturals, W types, and fixpoints
   5. CIC + Ω as alternative (w/ accessibility in as strict prop)
      <br/> (since equality reflection is only needed to show this via funext)
4. Type Preservation
   1. Recipe for proving preservation
   2. Compositionality lemmas
   3. Convertibility of reduction
   4. Convertibility of closure of reduction
   5. Preservation of convertibility
   6. Preservation of subtyping
   7. Preservation of sizes
   8. Preservation of typing
   9. Normalization and consistency
5. Extensions
   1. Function η-equivalences
   2. Pairs and equality/inductives
   3. Streams/coinductives
6. Outstanding issues
   1. Universe levels (fix: parametrized sizes?)
   2. Infinite size (fix: erasure? irrelevance? modality?)
7. Related work (see ISTCP?)
8. Conclusion

## TODOs

* Rewrite first paragraph in Discussion
* Fill in everything marked with `\TODO`
* Revisit `% TODO`s eventually
* Prove type preservation
* Prove confluence
* Ask William about replacement by reduction
* Restructure Design Shortcomings as a Discussion + Conclusion chapter
* Write Introduction chapter
* Add congruence rules in Appendix
* Fix index entries (a lot are probably missing) and glossary entries
* Lay Summary, Acknowledgements, Dedication