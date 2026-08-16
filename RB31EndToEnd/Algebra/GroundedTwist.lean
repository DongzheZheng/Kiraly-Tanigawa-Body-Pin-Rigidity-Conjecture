import RB31EndToEnd.Linear.PinRank
import RB31EndToEnd.Linear.TwistSystem

/-!
# Grounding the body-twist system

Fixing one body removes the six-dimensional diagonal subspace.  This
file proves that the resulting explicit linear operator is injective
exactly when the ungrounded pin system has only diagonal motions.
-/

namespace RB31E2E

variable {k W E : Type*} [Field k] [DecidableEq W]

/-- Bodies other than the selected grounded body. -/
abbrev OffRoot (root : W) := {w : W // w ≠ root}

/-- Extend an off-root assignment by zero at the grounded body. -/
def extendGrounded (root : W) (X : OffRoot root → Twist k) : W → Twist k :=
  fun w ↦ if h : w = root then 0 else X ⟨w, h⟩

@[simp] theorem extendGrounded_root (root : W) (X : OffRoot root → Twist k) :
    extendGrounded root X root = 0 := by
  simp [extendGrounded]

@[simp] theorem extendGrounded_offRoot (root : W) (X : OffRoot root → Twist k)
    (w : OffRoot root) :
    extendGrounded root X w.1 = X w := by
  simp [extendGrounded, w.2]

/-- Grounded extension as a linear map. -/
def extendGroundedLinear (root : W) :
    (OffRoot root → Twist k) →ₗ[k] (W → Twist k) where
  toFun := extendGrounded root
  map_add' X Y := by
    funext w
    by_cases h : w = root <;> simp [extendGrounded, h]
  map_smul' a X := by
    funext w
    by_cases h : w = root <;> simp [extendGrounded, h]

/-- Difference of two selected body twists. -/
def assignmentDifferenceLinear (u v : W) :
    (W → Twist k) →ₗ[k] Twist k where
  toFun X := X u - X v
  map_add' X Y := by simp; abel
  map_smul' a X := by simp [smul_sub]

/-- The explicit grounded pin-constraint operator. -/
noncomputable def groundedPinOperator (root : W) (src dst : E → W)
    (p : E → Vec3 k) :
    (OffRoot root → Twist k) →ₗ[k] (E → Vec3 k) :=
  LinearMap.pi fun e ↦
    (Twist.evalLinear (p e)).comp
      ((assignmentDifferenceLinear (src e) (dst e)).comp
        (extendGroundedLinear root))

@[simp] theorem groundedPinOperator_apply (root : W) (src dst : E → W)
    (p : E → Vec3 k) (X : OffRoot root → Twist k) (e : E) :
    groundedPinOperator root src dst p X e =
      Twist.eval
        (extendGrounded root X (src e) - extendGrounded root X (dst e)) (p e) := by
  simp [groundedPinOperator, assignmentDifferenceLinear, extendGroundedLinear]

theorem mem_ker_groundedPinOperator_iff (root : W) (src dst : E → W)
    (p : E → Vec3 k) (X : OffRoot root → Twist k) :
    X ∈ LinearMap.ker (groundedPinOperator root src dst p) ↔
      IsTwistMotion src dst p (extendGrounded root X) := by
  constructor
  · intro hX e
    have he := congrFun (LinearMap.mem_ker.mp hX) e
    simp only [groundedPinOperator_apply, Pi.zero_apply] at he
    rw [Twist.eval_sub] at he
    exact sub_eq_zero.mp he
  · intro hX
    rw [LinearMap.mem_ker]
    funext e
    simp only [groundedPinOperator_apply, Pi.zero_apply]
    rw [Twist.eval_sub]
    exact sub_eq_zero.mpr (hX e)

/-- Grounding converts diagonal-kernel rigidity into ordinary injectivity. -/
theorem groundedPinOperator_injective_iff_twistRigidAt
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    Function.Injective (groundedPinOperator root src dst p) ↔
      TwistRigidAt src dst p := by
  constructor
  · intro hinj X hX
    let Y : Twist k := X root
    let Z : OffRoot root → Twist k := fun w ↦ X w.1 - Y
    have hExtend : extendGrounded root Z = fun w ↦ X w - Y := by
      funext w
      by_cases hw : w = root
      · subst w
        simp [Z, Y]
      · simp [extendGrounded, hw, Z]
    have hZmotion : IsTwistMotion src dst p (extendGrounded root Z) := by
      intro e
      rw [hExtend]
      simp only [Twist.eval_sub]
      exact congrArg (fun z ↦ z - Twist.eval Y (p e)) (hX e)
    have hZker : Z ∈ LinearMap.ker (groundedPinOperator root src dst p) :=
      (mem_ker_groundedPinOperator_iff root src dst p Z).mpr hZmotion
    have hZzero : Z = 0 := by
      apply hinj
      rw [LinearMap.mem_ker] at hZker
      simpa using hZker
    refine ⟨Y, ?_⟩
    funext w
    have hAt := congrFun hExtend w
    rw [hZzero] at hAt
    simp only [Pi.zero_apply, extendGrounded, dite_eq_ite, ite_self] at hAt
    exact sub_eq_zero.mp hAt.symm
  · intro hrig
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro Z hZ
      have hMotion :=
        (mem_ker_groundedPinOperator_iff root src dst p Z).mp hZ
      obtain ⟨Y, hdiag⟩ := hrig (extendGrounded root Z) hMotion
      have hY : Y = 0 := by
        have hroot := congrFun hdiag root
        simpa using hroot.symm
      have hZzero : Z = 0 := by
        funext w
        have hw := congrFun hdiag w.1
        rw [hY] at hw
        simpa using hw
      simp [hZzero]
    · exact bot_le

end RB31E2E
