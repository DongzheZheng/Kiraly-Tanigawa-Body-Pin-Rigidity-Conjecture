import RB31EndToEnd.Algebra.LinearFormIdeal

/-!
# Height of a finite linear-form ideal

The explicit linear change of coordinates used to prove primality also
exhibits a prime chain of length equal to the row-space rank.  Only the
lower height bound needed by the selected-null argument is recorded here.
-/

namespace RB31E2E

namespace LinearFormIdeal

noncomputable section

open MvPolynomial
open NullCellulePolynomial

variable {k I : Type*} [Field k] [Fintype I] [DecidableEq I]

/-- A finite homogeneous linear row ideal has height at least the dimension
of its coefficient row span. -/
theorem finrank_span_le_linearFormIdeal_height
    {J : Type*} (row : J → I → k) :
    (Module.finrank k (Submodule.span k (Set.range row)) : ℕ∞) ≤
      (linearFormIdeal row).height := by
  classical
  let W := Submodule.span k (Set.range row)
  let r := Module.finrank k W
  let bW := Module.finBasis k W
  let family : Fin r → I → k := fun i ↦ (bW i : I → k)
  have hfamily : LinearIndependent k family := by
    exact bW.linearIndependent.map' W.subtype
      ((LinearMap.ker_eq_bot).2 W.subtype_injective)
  let bExt := Module.Basis.sumExtend hfamily
  let idx : (Fin r ⊕ Module.Basis.sumExtendIndex hfamily) ≃ I :=
    bExt.indexEquiv (Pi.basisFun k I)
  let bI : Module.Basis I k (I → k) := bExt.reindex idx
  let e : (I → k) ≃ₗ[k] (I → k) :=
    (Pi.basisFun k I).equiv bI (Equiv.refl I)
  let c : Fin r → I := fun i ↦ idx (Sum.inl i)
  have hc : Function.Injective c := by
    intro i j hij
    exact Sum.inl_injective (idx.injective hij)
  have he (i : Fin r) :
      e ((Pi.basisFun k I) (c i)) = family i := by
    dsimp [e, c]
    rw [Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply]
    dsimp [bI]
    rw [Module.Basis.reindex_apply]
    have hidx : idx.symm (idx (Sum.inl i)) = Sum.inl i :=
      idx.symm_apply_apply (Sum.inl i)
    rw [hidx]
    change (Module.Basis.sumExtend hfamily) (Sum.inl i) = family i
    rw [Module.Basis.sumExtend, Module.Basis.reindex_apply]
    simp only [Equiv.symm_symm]
    exact Module.Basis.extend_apply_self _ _
  have hX (i : Fin r) :
      linearChangeEquiv e (X (c i)) =
        linearPolynomial (family i) := by
    change linearChangeHom e (X (c i)) = _
    rw [linearChangeHom_X, he]
  have hmap :
      Ideal.map (linearChangeEquiv e).toRingEquiv
          (coordinateVariableIdeal (k := k) (Set.range c)) =
        Ideal.span (Set.range
          (fun i ↦ linearPolynomial (family i))) := by
    rw [coordinateVariableIdeal, Ideal.map_span]
    congr 1
    ext q
    constructor
    · rintro ⟨x, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, (hX i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨X (c i), ?_, ?_⟩
      · exact ⟨c i, ⟨i, rfl⟩, rfl⟩
      · simpa using hX i
  have hcoord : (r : ℕ∞) ≤
      (coordinateVariableIdeal (k := k) (Set.range c)).height :=
    coordinateVariableIdeal_height_ge_card (k := k) c hc
  have hlinear : (r : ℕ∞) ≤
      (Ideal.span (Set.range
        (fun i ↦ linearPolynomial (family i)))).height := by
    rw [← hmap, (linearChangeEquiv e).toRingEquiv.height_map]
    exact hcoord
  rw [linearFormIdeal_eq_basisIdeal row]
  simpa [W, r, bW, family] using hlinear

end

end LinearFormIdeal

end RB31E2E
