# Euclidean local and continuous rigidity

The closed Euclidean geometric theorems and their axiom dependencies have
been checked in the pinned Lean 4.29 environment on a remote server.

## Mathematical statement

Two labelled placements are equivalent when corresponding graph edges have
equal Euclidean lengths. They are congruent when every pairwise distance
agrees. A placement is locally rigid if all sufficiently close equivalent
placements are congruent to it.

For a finite simple graph `G` in any dimension `d`, the geometric theorem
equates the following properties:

1. There is an open dense set of placements at which `G` is locally rigid.
2. The maximum attained rigidity rank of `G` equals that of the complete graph
   on the same vertices.
3. There is an open dense set of placements from which every continuous
   edge-length-preserving motion remains congruent throughout.

Continuous motions are maps from the closed unit interval into the placement
space. No differentiability assumption is imposed. At every placement regular
for both the graph and the complete graph, local and continuous rigidity are
also proved equivalent pointwise.

Applied to the actual expanded body–pin graph, this equivalence transfers the
closed maximum-rank partition theorem to local and continuous Euclidean
rigidity. None of these properties is an additional hypothesis in the final
body–pin theorem.

The statement includes the empty vertex set and dimension zero. Comparison
with the complete graph avoids an incorrect large-framework rank formula in
these small cases. Local rigidity does not assert global rigidity: a distant
equivalent placement may fail to be congruent.

Regularity of the complete graph matters in a pointwise comparison. For
example, two unit bars forming a straight three-vertex path in three-space
have the same realized rank as the complete graph at that collinear
placement. One bar can nevertheless rotate about the middle vertex. The
complete graph is not regular there. The forward theorem compares with its
maximum attained rank, and the pointwise equivalence explicitly requires
regularity for both graphs.

## Definitions and theorem interfaces

| Interface | Mathematical content |
| --- | --- |
| `BarJoint.squaredLengthMap` | Squared Euclidean edge lengths, with zero coordinates on nonedges |
| `BarJoint.IsLocallyRigid` | Every sufficiently close equivalent placement is congruent |
| `BarJoint.IsRegularPlacement` | The graph's rigidity rank is maximal at this placement |
| `BarJoint.IsGenericPlacement` | Simultaneous regularity for every graph on the fixed finite vertex set |
| `BarJoint.IsGenericallyLocallyRigid` | Local rigidity throughout an open dense set of placements |
| `BarJoint.EuclideanIsGenericallyLocallyRigid` | The same open-dense property on native Euclidean placements |
| `BarJoint.EuclideanIsGenericallyContinuouslyRigid` | Continuous rigidity on an open dense set of native Euclidean placements |
| `endToEndGeometricBodyPinStatement` | The partition criterion in this geometric formulation |
| `endToEndContinuousBodyPinStatement` | The partition criterion in continuous Euclidean rigidity form |

Here “generic placement” means rank-generic, namely simultaneous regularity.
The set of such placements is proved open, dense, and nonempty. This definition
does not assert algebraic independence of the coordinates; those two notions
are not identified. The final open-dense geometric predicate contains no rank
condition in its definition.

The original coordinate type `Fin d → ℝ` carries the supremum norm. Edge
lengths instead use `EuclideanSpace ℝ (Fin d)` and its Euclidean norm. The
squared-distance formula, a continuous linear equivalence of placement
spaces, and the corresponding equivalence of neighbourhood-based local
rigidity definitions are proved explicitly. The final geometric root uses
native Euclidean placements. All placement spaces are finite-dimensional.

## Proof

The derivative of the squared-length map is twice the original rigidity
operator, so they have the same kernel and rank.

For the forward implication, let `p` and `q` be equivalent and let `m` be their
midpoint. The difference of their squared edge lengths equals twice the
rigidity operator at `m` applied to `q − p`. Thus `q − p` lies in the graph's
motion kernel at `m`. If `p` attains the complete graph's maximum rank, a rank
lower bound persists at nearby midpoints. The graph and complete-graph
kernels there coincide. Applying the same midpoint identity to every vertex
pair proves that `p` and `q` are congruent.

For the reverse implication, a finite-dimensional C¹ lemma is proved using
Mathlib's implicit function theorem and mean-value theorem. At a maximum-rank
point of a map `f`, project onto the derivative range and use complementary
kernel coordinates. The resulting inverse chart gives local fibre slices
whose tangent space is exactly the kernel of the derivative. A C¹ map `g`
constant on the local `f`-fibre therefore annihilates that kernel. Applying
this to graph and complete-graph squared lengths proves the required kernel
equality at regular locally rigid placements.

Finally, the maximum-rank locus is open and dense. For density, interpolate
from any placement toward one attaining maximum rank. An appropriate square
minor becomes a univariate polynomial that is nonzero at the latter endpoint.
Its finitely many roots cannot fill a small interval. The finite intersection
over all graphs gives the simultaneous regular locus.

For continuous motions, equality of the centered Gram matrices first gives
an ambient linear isometry carrying every placement difference to its
corresponding difference. This isometry intertwines the rigidity operators,
so their ranks agree. In a connected continuous family of equivalent placements containing a
maximum-rank placement, the congruent members consequently form a nonempty
set that is both open and closed. The whole family is congruent.

Conversely, the regular-fibre slice supplies paths of the form `t ↦ ψ(tz)`
inside the edge-length fibre. Continuous rigidity forces all pairwise
distances to be constant on these slices. Differentiating at the origin
recovers the required inclusion of motion kernels. The same slice theorem
supports both the local and continuous reverse implications.

## Verification boundary

`RB31Geometric` imports the original closed theorem and the new geometric
bridges. `RB31EndToEnd` remains the independent maximum-rank root. The existing
Comparator challenge continues to compare that maximum-rank statement;
it does not independently compare the new geometric statements.

The geometric trust test prints the new roots' types and foundational axiom
dependencies. The semantic test expands both statements to distances,
neighbourhoods, and continuous motions. No Asimow–Roth statement is introduced
as an axiom or supplied
as an external literature hypothesis. The proof is checked in the pinned
Lean 4.29 environment; it does not require upgrading the main project to
the separate rank-comparison package's toolchain.

The classical references are Asimow and Roth, [*The rigidity of graphs*
(1978)](https://doi.org/10.1090/S0002-9947-1978-0511410-9) and [*The rigidity of
graphs, II* (1979)](https://doi.org/10.1016/0022-247X(79)90108-2).
