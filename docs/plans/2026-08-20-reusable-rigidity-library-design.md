# Reusable rigidity library design

Date: 2026-08-20

## Outcome

Turn the released Király--Tanigawa body--pin formalization into a small,
versionable Lean library surface without destabilizing the closed proof.  The
existing `import RB31EndToEnd` entry point and theorem names remain valid.
Downstream Whiteley/Dress work imports only curated `RB31EndToEnd.API.*`
modules and treats every other transitive declaration as unsupported
implementation detail.

This first branch is deliberately a strangler layer, not a namespace rewrite.
It gives the current proof a stable outside boundary; later branches may move
internals behind that boundary without changing consumers.

## Evidence from the current repository

- 127 Lean files, of which 126 are production modules.
- 35,223 source lines, 213 local import edges, and 64 Mathlib import edges.
- The file-level import graph is acyclic, but the directory-level graph has one
  large strongly connected component spanning Algebra, Combinatorics,
  Incidence, Linear, NullCellule, Rigidity, Target, and TargetReduction.
- `RB31EndToEnd.lean` imports two modules directly and all 125 other production
  modules transitively.  It is therefore a capstone, not a suitable library
  prelude.
- A 33-module reusable core is already a strict dependency closure.  A further
  BodyPin domain layer can be assembled without importing the final target.

The architecture problem is therefore mixed responsibilities and accidental
transitive weight, not a cyclic Lean build.

## Requirements

### Functional

1. Preserve the v1 `RB31EndToEnd` import and closed theorem.
2. Provide granular facade modules for graph, Sparse22, linear, algebraic
   certificates, bar--joint rank, body--pin semantics, and body twists.
3. Keep the unconditional Király--Tanigawa theorem behind an explicit heavy
   facade rather than the default API prelude.
4. Promote the duplicated `0,3,5,6`/complete-framework arithmetic identity to
   a reusable provider module below the facade layer.
5. Provide a direct theorem-shaped BodyPin consumer endpoint rather than
   requiring downstream code to unfold `EndToEndBodyPinStatement`.
6. Check in a deterministic module dependency graph and a named public API
   contract.
7. Compile representative legacy and Dress-style consumers using only the
   intended imports.

### Non-functional

- No existing proof declaration is moved or renamed in phase 1.
- Public facades are aggregation modules only.  New declarations live in
  ordinary reusable provider modules, and production internals never import a
  facade.
- The default API facade must not import the end-to-end capstone.
- Trust scanning covers every production facade and the root axiom audit stays
  unchanged.
- Lean and Lake are never run locally.  Full verification runs on the less busy
  of cab16/cab17; for this branch that host is cab17.
- Generated dependency artifacts are deterministic and need only POSIX shell
  tools already required by the repository.

## Architecture

```text
Mathlib
  |
  +-- API.Graph -------- LooplessMultiGraph
  +-- API.Sparse22 ----- finite sparse-graph packet
  +-- API.Linear ------- finite row/block interfaces
  +-- API.Algebra ------ specialization and polynomial certificates
  +-- API.BarJoint ----- generic maximum-rank bar--joint semantics
  +-- API.BodyPin ------ incidence, capacities, partitions, expanded graph
  +-- API.BodyTwist ---- twist semantics and body/bar bridges
             |
             +---------- RB31EndToEnd.API  (light default prelude)

Internal proof engine (existing modules, unsupported surface)
             |
             +---------- API.Theorem       (explicit heavy import)
                            |
                            +-- legacy RB31EndToEnd root remains unchanged
```

The initial facade modules retain the existing `RB31E2E` namespace.  A facade
defines which declarations are supported; it cannot make Lean's transitively
imported declarations inaccessible.  The contract is an exhaustive declaration
whitelist whose exact types are exercised by isolated one-facade consumers.
It is also enforced by an import-layer check that rejects dependencies from
production internals back into `RB31EndToEnd.API` and rejects any transitive
path from a light facade to the capstone.

## Public modules

| Module | Supported purpose | Explicitly excluded |
|---|---|---|
| `RB31EndToEnd.API.Graph` | finite occurrence-level loopless multigraphs | BodyPin target assembly |
| `RB31EndToEnd.API.Sparse22` | reusable `(2,2)` sparse graph packet | provenance-flag induction |
| `RB31EndToEnd.API.Linear` | finite row systems, span stress, block kernels | private/outside attack states |
| `RB31EndToEnd.API.Algebra` | real specialization and finite polynomial certificates | chart-specific height transport |
| `RB31EndToEnd.API.BarJoint` | placements, rigidity operator/rank, generic rank | body--pin proof engine |
| `RB31EndToEnd.API.BodyPin` | incidence, `pinCapacity`, finite partitions, expanded graph | capstone proof |
| `RB31EndToEnd.API.BodyTwist` | twists, pin-rank bounds, body/bar semantic bridges | null-cellule/provenance assembly |
| `RB31EndToEnd.API` | all lightweight supported modules above | `API.Theorem` |
| `RB31EndToEnd.API.Theorem` | unconditional body--pin equivalence and direct corollary | no additional attack internals promised |

## Whiteley/Dress consumer boundary

The current theorem supplies a completed BodyPin adapter, not the eventual
Whiteley/Dress semantic core.  Future target branches must add rank-valued
interfaces for arbitrary edge sets, closure, the cofactor rank system, maximal
cliques, and hinges.  They may depend on `API.Graph`, `API.BarJoint`,
`API.Linear`, and `API.Algebra`; they must not import the BodyPin capstone or
provenance-flag engine.

The immediate Dress consumer can delete duplicate arithmetic by defining its
existing `bodyPinEll` and `completeSeparatorRank` names as thin wrappers around
`pinCapacity` and `BarJoint.completeFrameworkRankTarget 3`.  The bridge theorem
lives in `RB31EndToEnd.Rigidity.BodyPinRankAccounting`; `API.BodyPin` merely
aggregates it.  The consumer's finite-complex and ordered-interface abstractions
remain independent because the provider has no equivalent public carrier yet.

## Failure modes and controls

| Failure | Control |
|---|---|
| A facade accidentally imports the root and becomes heavy | default-prelude import lint plus closure report |
| Old consumers break | legacy smoke test imports only `RB31EndToEnd` and checks the old theorem type |
| API names silently drift | public consumer smoke test and named API manifest |
| New production files bypass the trust scan | keep facades under `RB31EndToEnd/`; scan that complete tree |
| Dependency graph becomes stale | deterministic generator runs in `verify.sh --check` |
| Formal build differs from local inspection | all Lean verification on cab17 with the pinned 4.29.0 toolchain |
| Maximum real rank is overclaimed as a full rigidity matroid API | document the missing arbitrary-edge-set rank/closure bridge |
| A public release has unclear reuse rights | choose and add a license before the next public release; do not infer one in this branch |

## Deferred surgical cuts

After downstream smoke tests prove the facade useful, three high-value cuts can
be made without changing public theorem types:

1. Move `SparseNullIncidence.IsIncidenceRealization` out of
   `SmallBundleCertificate`, breaking the
   `UniversalHomogeneousChart -> SmallBundleCertificate -> TargetReduction`
   back edge.
2. Move the generic `quotientCoefficientMap` packet from
   `ActivePinPrimeHeight` into Algebra.
3. Split generic weighted-initial definitions from the NullCellule triangle
   and K4 replacement tables.

Those cuts are phase 2 because none is required to give current consumers a
light stable entry point.
