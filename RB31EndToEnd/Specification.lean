import Mathlib

/-!
# Body--pin incidence and partition capacity

This file defines finite loopless body--pin incidences, the capped bundle
capacity, and the partition condition.
-/

namespace RB31E2E

/-- The capped rank contribution of a bundle of body--pin occurrences. -/
def pinCapacity : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 6

/--
A finite loopless body--pin multigraph represented by a finite type of
pin occurrences and its two distinct body endpoints.  Using occurrences
instead of quotient-valued multiedges keeps every pin's provenance.
-/
structure BodyPinIncidence where
  Body : Type
  Pin : Type
  bodyFinite : Fintype Body
  pinFinite : Fintype Pin
  bodyDecidableEq : DecidableEq Body
  pinDecidableEq : DecidableEq Pin
  left : Pin → Body
  right : Pin → Body
  loopless : ∀ e, left e ≠ right e

attribute [instance] BodyPinIncidence.bodyFinite
attribute [instance] BodyPinIncidence.pinFinite
attribute [instance] BodyPinIncidence.bodyDecidableEq
attribute [instance] BodyPinIncidence.pinDecidableEq

/-- Multiplicity of pins whose unordered endpoints lie in `A` and `B`. -/
def BodyPinIncidence.crossingMultiplicity
    (H : BodyPinIncidence) (A B : Finset H.Body) : ℕ :=
  (Finset.univ.filter fun e =>
    (H.left e ∈ A ∧ H.right e ∈ B) ∨
    (H.left e ∈ B ∧ H.right e ∈ A)).card

/-- Capacity of one pair of disjoint body sets. -/
def BodyPinIncidence.crossingCapacity
    (H : BodyPinIncidence) (A B : Finset H.Body) : ℕ :=
  pinCapacity (H.crossingMultiplicity A B)

/--
Multiplicity of the pin bundle between two labelled blocks.  The
definition is symmetric in `i` and `j`; the pins themselves remain an
occurrence type, so no provenance is lost by aggregation.
-/
def BodyPinIncidence.bundleMultiplicity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) : ℕ :=
  (Finset.univ.filter fun e =>
    (π (H.left e) = i ∧ π (H.right e) = j) ∨
    (π (H.left e) = j ∧ π (H.right e) = i)).card

/-- Capacity of the pin bundle joining two labelled blocks. -/
def BodyPinIncidence.bundleCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) : ℕ :=
  pinCapacity (H.bundleMultiplicity π i j)

/--
Multiplicity indexed by an unordered pair of block labels.  Diagonal
pairs are allowed at this level and are discarded by
`partitionCapacity`.
-/
def BodyPinIncidence.unorderedBundleMultiplicity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (b : Sym2 (Fin t)) : ℕ :=
  (Finset.univ.filter fun e => s(π (H.left e), π (H.right e)) = b).card

/--
The capacity sum over unordered distinct block pairs.  This is the
literal left hand side of the body--pin partition conjecture.
-/
def BodyPinIncidence.partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) : ℕ :=
  ∑ b ∈ (⊤ : SimpleGraph (Fin t)).edgeFinset,
    pinCapacity (H.unorderedBundleMultiplicity π b)

/--
The capacity sum over ordered distinct block pairs.  Each unordered
pair occurs twice.  This convention avoids making an arbitrary order
part of a set partition.
-/
def BodyPinIncidence.orderedPartitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) : ℕ :=
  ∑ i : Fin t, ∑ j ∈ Finset.univ.erase i, H.bundleCapacity π i j

/--
The body--pin partition condition, expressed through surjective block
labels.  Surjectivity says that all `t` labels are actual blocks.  For
an empty body type the sole zero-block partition is included and the
natural-number right hand side is zero.
-/
def BodyPinIncidence.PartitionCondition (H : BodyPinIncidence) : Prop :=
  ∀ (t : ℕ) (π : H.Body → Fin t), Function.Surjective π →
    6 * (t - 1) ≤ H.partitionCapacity π

/-- The exactly doubled, ordered-pair audit form of the same condition. -/
def BodyPinIncidence.OrderedPartitionCondition (H : BodyPinIncidence) : Prop :=
  ∀ (t : ℕ) (π : H.Body → Fin t), Function.Surjective π →
    12 * (t - 1) ≤ H.orderedPartitionCapacity π

theorem BodyPinIncidence.bundleMultiplicity_comm
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) :
    H.bundleMultiplicity π i j = H.bundleMultiplicity π j i := by
  simp only [bundleMultiplicity, or_comm]

theorem BodyPinIncidence.bundleCapacity_comm
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) :
    H.bundleCapacity π i j = H.bundleCapacity π j i := by
  simp only [bundleCapacity, H.bundleMultiplicity_comm π i j]

end RB31E2E
