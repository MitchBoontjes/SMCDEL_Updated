# SMCDEL Changelog

## upcoming

New:

- Language: add global modality `G`

Changed:

- More haddock documentation
- Language: Remove `PubAnnounceW`, `Announce` and `AnnounceW`
- Improve `pubAnnounceTest` and `groupAnnounceTest`
- Bug fix: in `transformerToActionModelWithG` do not filter
- Bug fix: in `bddOf` for `Dia` use `unsafeUpdate`
- Bug fix in HasCacBDD-0.3.0.0: segfault on Apple M1 and ARM

## v1.3.0 (2024-04-24)

New:

- ZDDs as alternative in `SMCDEL.Symbolic.S5_CUDD` and `SMCDEL.Symbolic.K_CUDD` (by @dushiel)
- `SMCDEL.Symbolic.Ki` and `SMCDEL.Symbolic.Ki_CUDD` using one agent-indexed DD (by @dushiel)
- `SMCDEL.Symbolic.S5_DD`: using the pure Haskell `decision-diagrams` library
- Examples: add generalised versions of Sum and Product and Dining Cryptographers
- Web and CLI: add `ONEOF` keyword to allow formulas like `ONEOF (p, q, r)` - fix #21
- Web and CLI: allow lists after Kw for formulas like `bob knows whether (p, q)`
- Add gitpod and devcontainer configurations
- Haddock documentation, replacing the literate Haskell PDF document
- Add `D` and `Dw` operators for distributed knowledge (by @foxyseta and @BasLaa)
- Multipointed models and structures for S5

Changed:

- Web UI improvements: syntax highlighting, vertically maximized
- Use `defaultVocabulary` also for random Boolean formulas (and thus BDDs)
- Use `open` instead of hardcoding Okular
- Use newer HasCacBDD with faster `sizeOf`
- Bug fixes in `simStep`

## v1.2.0 (2022-02-22)

New:

- "TRUE?" command in Web and CLI interface to check truth at a single state
- multipointed translations for S5, including action models
- `instance Optimizable` for symbolic structures
- provide `whereViaBdd` also in `SMCDEL.Symbolic.S5_CUDD`
- sanity check input for Web and CLI interface
- integration tests for web interface

Changed:

- improve test coverage
- correction to Cheryl's Birthday example
- new definitions and functions for `MultipointedEvent = (Transformer,Bdd)`
- swapped argument order of `icSolves`
- use HasCacBDD-0.1.0.3
- update ace.js and MathJax
- check if dot2tex is available before using it
- compile web with -threaded to prevent the error `file descriptor ... out of range`
- bugfix in `SMCDEL.Internal.Help.set`
- bugfix in `SMCDEL.Translations.S5.actionToTransformerWithMap` to fix #17
- test coverage and bugfix for `SMCDEL.Symbolic.S5.generatedSubstructure`
- do not shrink to empty models
- web: listen only on 127.0.0.1, use PORT env variable

## v1.1.0 (2019-12-09)

New:

- minimization under bisimulation
- dynamic operators in formulas via `Data.Dynamic`
- multipointed models, action models, structures and events
- added Cheryl's Birthday and Cheryl's Age examples
- experimental functions for epistemic planning (with small examples)
- more instances for QuickCheck, more tests
- add S5 to K conversion in `SMCDEL.Translations.Convert`
- improvements to the web interface

Changed:

- polymorphic `update` replaces `productUpdate`, `transform`, `pubAnnounce` etc.
- factual change by default: merge `Symbolic.S5.Change` into `Symbolic.S5` etc.
- remove changeprops in (Kn)Trf to avoid redundancy with changelaw
- move BDD related functions to HasCacBDD (`substit`, `substitSimul`)
- avoid `Data.Map` in S5 modules, no longer depend on `lens`
- replace `.cabal` file with a `package.yml` for `hpack`


## v1.0.0  (2018-02-26)

New:

- action models and transformers with factual change
- NonS5 modules, now called K, are no longer experimental
- separate types State and World
- automated testing and benchmarks
- lots of bugfixes

Removed:

- removed support for robbed, NooBDD and Z3
- old Example files


## v0.2  (2015-11-17)

First release with a standalone-executable.


## v0.1  (2015-09-21)

The first public version of SMCDEL. Note that this version does not contain a
stand-alone executable. It can only be used as a Haskell library.
