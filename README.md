# Three-dimensional body--pin rigidity

This repository contains a Lean 4 formalization of the partition
characterization of generic infinitesimal rigidity for three-dimensional
body--pin frameworks.

## The theorem

Let `H` be a finite loopless body--pin multigraph. Each pin occurrence becomes
a shared vertex, and each body `w` receives four private vertices together with
an arbitrary number `r(w)` of additional private vertices. The vertices
belonging to each body induce a clique; their union is the expanded simple graph
`G(H,r)`.

For a bundle of `n` pins between two blocks, set

```text
c(0) = 0,  c(1) = 3,  c(2) = 5,  c(n) = 6 for n >= 3.
```

The formalized theorem states that, for every `H` and every choice of `r`, the
maximum ranks attained by the real rigidity matrices of `G(H,r)` and of the
complete graph on the same vertex set are equal if and only if every partition
of the bodies into `t` nonempty blocks satisfies

```text
6(t - 1) <= sum c(m_ij),
```

where the sum ranges over unordered pairs of distinct blocks and `m_ij` is the
number of pins joining blocks `i` and `j`. Parallel pins, the empty body set,
and the one-body case are included in the statement.

The Lean theorem is the maximum-rank formulation of generic infinitesimal
rigidity. No generic configuration is chosen in the statement: generic rank is
defined as the maximum rank attained by the real rigidity matrix.

The classical Asimow--Roth passage to generic rigidity in the usual geometric
sense is not included in the current formalization.

## Scope of the formalization

Both implications are proved. The sufficiency proof includes the collinearity-
flag semismallness theorem, the exact primewise height formula for the minimal
primes of the rational selected null-difference ideals that survive a complete
pairwise-distinctness chart, and the exclusion of exceptional pin parameters.
None of these results is supplied as an assumption to the root theorem.

The core library contains the transitive source dependency closure of the
end-to-end theorem, together with a small trust audit. Experimental files and
historical proof routes are not part of this release. `RB31Interop` is a
separate, theorem-independent compatibility target.

## Requirements

- [elan](https://lean-lang.org/lean4/doc/setup.html)
- Git
- a POSIX shell with Bash

The checked-in toolchain and manifest pin the environment to:

- Lean `4.29.0`
- mathlib commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`

## Reproduce the proof

```bash
./scripts/setup.sh
./scripts/verify.sh
```

The first command downloads the pinned dependencies and the matching mathlib
cache. The second checks the source manifest, scans the production sources,
builds the complete theorem and interoperability target with warnings treated
as errors, builds the Comparator statement and solution modules, and checks the
type and axiom dependencies of the closed root theorem. The scripts may be run
from any working directory.

Individual stages are also available:

```bash
./scripts/trust-scan.sh
./scripts/build.sh
./scripts/audit.sh
```

Run `./scripts/source-manifest.sh` to regenerate the deterministic SHA-256
manifest of the source-only release.

GitHub Actions runs the same build and audit on every push and pull request.

## Interoperability

`RB31Interop` exports the occurrence-indexed body multigraph as mathlib's
`Graph H.Body H.Pin`, the interface used by
[CombinatorialRigidity](https://github.com/bryangingechen/CombinatorialRigidity)
for body-level multigraphs. All bodies and pin occurrences remain present, and
parallel pins remain distinct. The expanded bar--joint graph is already a
mathlib `SimpleGraph`, so no conversion is required at that layer.

The exact interface and the current toolchain boundary are documented in
[`docs/INTEROPERABILITY.md`](docs/INTEROPERABILITY.md).

## Comparator surface

`Challenge.lean`, `Solution.lean`, and `comparator.json` provide the independent
statement/solution layout expected by
[leanprover/comparator](https://github.com/leanprover/comparator). The challenge
imports only Mathlib and contains the complete mathematical statement surface;
the solution supplies the proof from the production development. Comparator is
configured to permit exactly `propext`, `Quot.sound`, and `Classical.choice`.

With Comparator, a Lean-4.29-compatible `lean4export`, and Landrun installed,
run the separate declaration comparison on Linux:

```bash
./scripts/compare.sh /absolute/path/to/comparator
```

The statement comparison and default-kernel recheck were tested with Comparator
commit `2312244ac716564a61cc0bf4e107d9abf1757a61` and `lean4export` commit
`5a53b634f6a3e21e55b4852337c4fcf0781ad1aa` (tag `v4.29.0`). The server test
used Comparator's development runner; independent security review should use
the sandbox setup described in the upstream instructions. `verify.sh` builds
both modules but does not install or run Comparator.

[`formalization.yaml`](formalization.yaml) supplies the project metadata,
statement alignment, and declared verification scope for registry review.

## Trust boundary

The production development adds no mathematical axioms. It does not use
`sorry`, `admit`, an explicit `opaque` declaration, or an external oracle in
place of a load-bearing proof. The structure fields for collinearity-flag
states and function-field branches do not contain the semismallness or height
conclusions that they are used to prove. `Challenge.lean` contains the single
deliberate placeholder in the Comparator challenge; it is not imported by the
proof library or by `Solution.lean`.

The closed root theorem depends exactly on `propext`, `Classical.choice`, and
`Quot.sound`. These are Lean's principles of propositional extensionality,
classical choice, and compatibility of quotient types. All project and mathlib
declarations used by the proof are checked by the Lean kernel.

## Repository layout

- `RB31EndToEnd.lean` states the unconditional root theorem.
- `RB31EndToEnd/` contains the proof modules.
- `RB31Interop.lean` is the optional mathlib `Graph` compatibility entry point.
- `Challenge.lean`, `Solution.lean`, and `comparator.json` define the Comparator
  statement/proof boundary.
- `Tests/Trust.lean` records the root type and its axiom dependencies.
- `scripts/` contains setup, build, source-scan, and audit commands.
- `SOURCE_MANIFEST.sha256` records the released source files.
- `.github/workflows/lean.yml` provides continuous verification.
- `CITATION.cff` supplies citation metadata for the formalization.

## License

Copyright 2026 Dongzhe (Denzel) Zheng. Licensed under the
[Apache License, Version 2.0](LICENSE).
