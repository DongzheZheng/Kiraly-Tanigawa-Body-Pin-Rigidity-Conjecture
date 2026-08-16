import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The kernel exact sequence for a two-by-two block map

This file isolates the linear-algebra mechanism used when a live vertex is
deleted from a direction matrix.  For maps

`A : X → Y`, `B : Z → Y`, and `C : Z → W`,

the block map sends `(x,z)` to `(A x + B z, C z)`.  Its kernel maps to the
kernel of the connecting map

`ker C → Y / range A`, `z ↦ [B z]`.

The resulting short exact sequence is proved literally, including the
surjectivity lift and the identification of its kernel with `ker A`.  No
dimension identity is stored as a hypothesis.
-/

namespace RB31E2E

namespace BlockKernelExact

noncomputable section

variable {k X Z Y W : Type*} [Field k]
  [AddCommGroup X] [Module k X]
  [AddCommGroup Z] [Module k Z]
  [AddCommGroup Y] [Module k Y]
  [AddCommGroup W] [Module k W]

/-- The lower-triangular block map `(x,z) ↦ (A x + B z, C z)`. -/
def blockMap (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    (X × Z) →ₗ[k] (Y × W) where
  toFun p := (A p.1 + B p.2, C p.2)
  map_add' p q := by
    apply Prod.ext
    · simp only [map_add, Prod.fst_add, Prod.snd_add]
      abel
    · simp
  map_smul' c p := by
    ext <;> simp

@[simp]
theorem blockMap_apply
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W)
    (p : X × Z) :
    blockMap A B C p = (A p.1 + B p.2, C p.2) := rfl

/-- The connecting map from the local kernel to the old-row cokernel. -/
def connectingMap (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker C →ₗ[k] (Y ⧸ LinearMap.range A) where
  toFun z := (LinearMap.range A).mkQ (B z.1)
  map_add' z z' := by simp
  map_smul' c z := by simp

@[simp]
theorem connectingMap_apply
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W)
    (z : LinearMap.ker C) :
    connectingMap A B C z = (LinearMap.range A).mkQ (B z.1) := rfl

/-- Project a block-kernel element to its local coordinate.  The block
equation says that its connecting class vanishes. -/
def kernelToConnecting
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker (blockMap A B C) →ₗ[k] LinearMap.ker (connectingMap A B C) where
  toFun p := by
    refine ⟨⟨p.1.2, ?_⟩, ?_⟩
    · have hp := LinearMap.mem_ker.mp p.2
      exact congrArg Prod.snd hp
    · rw [LinearMap.mem_ker]
      have hp := LinearMap.mem_ker.mp p.2
      have hfirst : A p.1.1 + B p.1.2 = 0 := congrArg Prod.fst hp
      change (LinearMap.range A).mkQ (B p.1.2) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨-p.1.1, ?_⟩
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right hfirst
  map_add' p q := by
    ext
    rfl
  map_smul' c p := by
    ext
    rfl

@[simp]
theorem kernelToConnecting_coe
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W)
    (p : LinearMap.ker (blockMap A B C)) :
    ((kernelToConnecting A B C p : LinearMap.ker C) : Z) = p.1.2 := rfl

/-- Every vanishing connecting class lifts to a block-kernel element. -/
theorem kernelToConnecting_surjective
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    Function.Surjective (kernelToConnecting A B C) := by
  intro z
  have hzq : (LinearMap.range A).mkQ (B z.1) = 0 := by
    exact LinearMap.mem_ker.mp z.2
  have hzrange : B z.1 ∈ LinearMap.range A :=
    (by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzq
      exact hzq)
  obtain ⟨x, hx⟩ := hzrange
  let p : X × Z := (-x, z.1)
  have hp : p ∈ LinearMap.ker (blockMap A B C) := by
    rw [LinearMap.mem_ker]
    apply Prod.ext
    · change A (-x) + B z.1 = 0
      rw [map_neg]
      rw [hx]
      simp
    · dsimp [p]
      exact LinearMap.mem_ker.mp z.1.2
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Insert an old-kernel vector as a block-kernel vector with zero local
coordinate. -/
def oldKernelToBlockKernel
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker A →ₗ[k] LinearMap.ker (blockMap A B C) where
  toFun x := by
    refine ⟨(x.1, 0), ?_⟩
    rw [LinearMap.mem_ker]
    ext <;> simp [LinearMap.mem_ker.mp x.2]
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

/-- The old kernel is linearly equivalent to the kernel of the projection
from block stresses to local connecting stresses. -/
def oldKernelEquivProjectionKernel
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker A ≃ₗ[k] LinearMap.ker (kernelToConnecting A B C) where
  toFun x := by
    refine ⟨oldKernelToBlockKernel A B C x, ?_⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  invFun p := by
    refine ⟨p.1.1.1, ?_⟩
    have hproj := LinearMap.mem_ker.mp p.2
    have hz : p.1.1.2 = 0 := by
      have hproj' : kernelToConnecting A B C p.1 = 0 := hproj
      exact congrArg
        (fun z : LinearMap.ker (connectingMap A B C) ↦
          ((z.1 : LinearMap.ker C).1 : Z)) hproj'
    have hblock := LinearMap.mem_ker.mp p.1.2
    have hfirst : A p.1.1.1 + B p.1.1.2 = 0 := congrArg Prod.fst hblock
    rw [hz] at hfirst
    simpa using hfirst
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hproj := LinearMap.mem_ker.mp p.2
      have hz : p.1.1.2 = 0 := by
        have hproj' : kernelToConnecting A B C p.1 = 0 := hproj
        exact congrArg
          (fun z : LinearMap.ker (connectingMap A B C) ↦
            ((z.1 : LinearMap.ker C).1 : Z)) hproj'
      exact hz.symm
  map_add' x y := by
    ext <;> simp [oldKernelToBlockKernel]
  map_smul' c x := by
    ext <;> simp [oldKernelToBlockKernel]

/-- Exact kernel dimension formula for the block map. -/
theorem finrank_blockKernel
    [FiniteDimensional k X] [FiniteDimensional k Z]
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    Module.finrank k (LinearMap.ker (blockMap A B C)) =
      Module.finrank k (LinearMap.ker A) +
        Module.finrank k (LinearMap.ker (connectingMap A B C)) := by
  have hRN := (kernelToConnecting A B C).finrank_range_add_finrank_ker
  have hsurj : LinearMap.range (kernelToConnecting A B C) = ⊤ :=
    LinearMap.range_eq_top.mpr (kernelToConnecting_surjective A B C)
  have hker : Module.finrank k (LinearMap.ker (kernelToConnecting A B C)) =
      Module.finrank k (LinearMap.ker A) :=
    (oldKernelEquivProjectionKernel A B C).finrank_eq.symm
  rw [hsurj, finrank_top, hker] at hRN
  omega

end

end BlockKernelExact

end RB31E2E
