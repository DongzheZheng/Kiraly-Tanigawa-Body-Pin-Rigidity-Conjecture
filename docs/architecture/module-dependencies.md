# Lean module dependencies

## Checked artifact

`import-graph.dot` is the deterministic, source-derived graph of every Lean
module in this checkout, including tests.  An edge

```text
A -> B
```

means that module `A` directly imports project-local module `B`.  Mathlib
imports are intentionally omitted.  Every module is emitted as a node, even if
it has no project-local import.  Nodes and edges use bytewise lexical order, and
the file contains no timestamp or machine-specific path.

Regenerate and check it with:

```bash
./scripts/module-deps.sh --write
./scripts/module-deps.sh --check
./scripts/api-layer-check.sh
./scripts/api-layer-check.sh --self-test
```

These commands only inspect text.  They do not invoke Lean or Lake.  The source
search prunes both `.lake` and `.git`; the latter is handled whether it is a
directory in a normal clone or a metadata file in a Git worktree.

## Audit baseline

Before adding the facade modules, the repository contained 127 Lean files,
213 project-local import edges, and 64 Mathlib import commands.  The 126
production modules formed an acyclic file-level graph.  The legacy
`RB31EndToEnd` root had two direct imports and a transitive closure containing
all other 125 production modules.  Its longest import path had 23 edges.

Directory names did not form dependency layers.  At directory granularity,
`Algebra`, `Combinatorics`, `Incidence`, `Linear`, `NullCellule`, `Rigidity`,
`Target`, and `TargetReduction` belonged to one strongly connected component,
even though the underlying module graph was acyclic.  This is why the first
library boundary is a facade rather than a physical directory move.

## Facade closure sizes

The checked post-facade graph gives the following transitive project-module
closures, counting the facade itself:

| Import | Modules |
|---|---:|
| `RB31EndToEnd.API.Graph` | 2 |
| `RB31EndToEnd.API.BarJoint` | 2 |
| `RB31EndToEnd.API.Linear` | 5 |
| `RB31EndToEnd.API.BodyPin` | 8 |
| `RB31EndToEnd.API.Sparse22` | 10 |
| `RB31EndToEnd.API.Algebra` | 12 |
| `RB31EndToEnd.API.BodyTwist` | 14 |
| `RB31EndToEnd.API` | 46 |
| legacy `RB31EndToEnd` | 126 |
| explicit `RB31EndToEnd.API.Theorem` | 127 |

Thus a BodyPin model consumer loads eight project modules instead of the full
126-module proof, while the all-reusable prelude remains a 46-module closure.
The capstone stays intentionally heavy and explicit.

## Dependency policy

The supported direction is:

```text
Mathlib
  |
  +-- reusable implementation modules
  |     Graph / Sparse22 / Linear / Algebra / BarJoint
  |
  +-- BodyPin and BodyTwist domain adapters
  |
  +-- RB31EndToEnd.API.* lightweight facades
  |        |
  |        +-- RB31EndToEnd.API lightweight prelude
  |
  +-- legacy proof engine and end-to-end root
           |
           +-- RB31EndToEnd.API.Theorem explicit capstone facade
```

Facade files are consumer-facing aggregation modules.  Production
implementation files outside `RB31EndToEnd/API*` must never import them.
`RB31EndToEnd/API.lean` and every lightweight granular facade must not import
the legacy `RB31EndToEnd` root or `RB31EndToEnd.API.Theorem`, either directly
or through any project module in their transitive import closure.  Only the
theorem facade is allowed to cross that boundary.

The aggregate `RB31EndToEnd.API` prelude has a stricter direct-import
contract.  Its project-local imports must be exactly this order-independent
set, with no missing, additional, or duplicate member:

```text
RB31EndToEnd.API.Graph
RB31EndToEnd.API.Sparse22
RB31EndToEnd.API.Linear
RB31EndToEnd.API.Algebra
RB31EndToEnd.API.BarJoint
RB31EndToEnd.API.BodyPin
RB31EndToEnd.API.BodyTwist
```

`scripts/api-layer-check.sh` builds the live project-local import graph from
the Lean sources and performs a breadth-first reachability search from every
lightweight facade.  A violation reports a deterministic witness path from the
facade to the root or theorem facade.  The check does not trust the checked-in
DOT, because that artifact could itself be stale.  Direct import scans remain
in place to give file-and-line diagnostics and to reject every production
implementation import of `RB31EndToEnd.API` or one of its children.  Import
tokens are parsed exactly rather than by substring, so `RB31EndToEnd.API` is
distinguished from `RB31EndToEnd`.  The same parsed graph supplies the
order-independent exact-set check for the aggregate prelude; a consumer smoke
test alone cannot prove that all seven direct imports remain present.

The `--self-test` mode is shell-only.  It builds temporary positive and
negative source fixtures: the positive graph keeps a light facade below the
capstone; one negative fixture makes an implementation import a facade; and
two more hide routes to the legacy root and to `API.Theorem` behind
intermediate modules.  Two aggregate-contract fixtures respectively omit one
required facade and add one unexpected facade.  All negative cases must fail;
the transitive witness paths and aggregate diagnostics are checked.  No
fixture invokes Lean or Lake.

## Closed reusable core

The following 33 pre-facade modules are a strict project-local dependency
closure.  They are the evidence behind the lightweight Graph, Sparse22,
Linear, Algebra, and BarJoint facades.

```text
RB31EndToEnd.Graph.LooplessMultiGraph

RB31EndToEnd.Combinatorics.Sparse22.Basic
RB31EndToEnd.Combinatorics.Sparse22.Construction
RB31EndToEnd.Combinatorics.Sparse22.DegreeThreeAugmentation
RB31EndToEnd.Combinatorics.Sparse22.GraphExtension
RB31EndToEnd.Combinatorics.Sparse22.OptimalPartition
RB31EndToEnd.Combinatorics.Sparse22.TightCompletion
RB31EndToEnd.Combinatorics.Sparse22.Transport
RB31EndToEnd.Combinatorics.Sparse22.TriangleSequence
RB31EndToEnd.Combinatorics.Sparse22.Uncrossing

RB31EndToEnd.Linear.BlockKernelExact
RB31EndToEnd.Linear.DirectionResponse
RB31EndToEnd.Linear.DirectionResponseBaseChange
RB31EndToEnd.Linear.DirectionStress
RB31EndToEnd.Linear.DirectionStressBaseChange
RB31EndToEnd.Linear.DirectionStressDeletion
RB31EndToEnd.Linear.FiniteFamilyBaseChange
RB31EndToEnd.Linear.FiniteRowSpanStress
RB31EndToEnd.Linear.FiniteRowSystem
RB31EndToEnd.Linear.PinFibres
RB31EndToEnd.Linear.TwistSystem
RB31EndToEnd.Linear.Vec3Twist

RB31EndToEnd.Algebra.AffineSpanDescent
RB31EndToEnd.Algebra.AlgebraicIndependentAffine
RB31EndToEnd.Algebra.ComplexRealSpecialization
RB31EndToEnd.Algebra.CoordinateFieldTower
RB31EndToEnd.Algebra.FiniteChartCertificates
RB31EndToEnd.Algebra.FiniteCoordinateTrdeg
RB31EndToEnd.Algebra.FiniteOpenIntersection
RB31EndToEnd.Algebra.FractionQuotientCoordinates
RB31EndToEnd.Algebra.PolynomialPrimeTrdegHeight
RB31EndToEnd.Algebra.RationalCertificateDescent

RB31EndToEnd.Rigidity.BarJoint
```

An optional six-module Split--Klein polynomial packet extends that closure to
39 modules:

```text
RB31EndToEnd.NullCellule.Definitions
RB31EndToEnd.NullCellule.PolynomialModel
RB31EndToEnd.NullCellule.ReplacementIdentities
RB31EndToEnd.NullCellule.WeightComponents
RB31EndToEnd.NullCellule.VertexK4Weight
RB31EndToEnd.NullCellule.WeightInitialIdeal
```

This second packet is reusable but semantically narrower, so it is not part of
the default phase-one facade.

## Known phase-two cuts

Three mixed-responsibility imports account for disproportionate transitive
weight and should be split only after consumers validate the facade contract:

1. `Algebra.FilteredInitialHeight` imports
   `NullCellule.WeightInitialIdeal`, pulling the replacement packet into
   otherwise generic weighted-initial algebra.
2. `Algebra.MinimalPrimeLinearFibre` imports
   `Incidence.ActivePinPrimeHeight` for the generic coefficient-quotient map
   packet and thereby acquires 42 project dependencies.
3. `Incidence.SmallBundleCertificate` contains generic sparse-null incidence
   semantics, a BodyPin adapter, and end-to-end assembly in one file.  Its
   `TargetReduction` import is consequently pulled into
   `Incidence.UniversalHomogeneousChart`.

The checked facade boundary makes these later extractions possible without
changing consumer imports.
