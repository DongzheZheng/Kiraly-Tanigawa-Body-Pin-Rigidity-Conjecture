import RB31EndToEnd.API.Linear

/-! A consumer of the public finite linear-algebra facade and no other project facade. -/

namespace PublicAPISmoke.Linear

noncomputable def matrix
    {k I J : Type*} [Field k] [Fintype I] [Fintype J]
    (row : J → I → k) : Matrix J I k :=
  RB31E2E.FiniteRowSystem.matrix row

noncomputable def constraint
    {k I J : Type*} [Field k] [Fintype I] [Fintype J]
    (row : J → I → k) : (I → k) →ₗ[k] (J → k) :=
  RB31E2E.FiniteRowSystem.constraint row

noncomputable def synthesis
    {k I J : Type*} [Field k] [Fintype I] [Fintype J]
    (row : J → I → k) : (J → k) →ₗ[k] (I → k) :=
  RB31E2E.FiniteRowSystem.synthesis row

noncomputable def stressDim
    {k I J : Type*} [Field k] [Fintype I] [Fintype J]
    (row : J → I → k) : ℕ :=
  RB31E2E.FiniteRowSystem.stressDim row

example {k I J : Type*} [Field k] [Fintype I] [Fintype J]
    (row : J → I → k) :
    Module.finrank k
        (LinearMap.range (RB31E2E.FiniteRowSystem.constraint row)) =
      Module.finrank k
        (LinearMap.range (RB31E2E.FiniteRowSystem.synthesis row)) :=
  RB31E2E.FiniteRowSystem.finrank_range_constraint_eq_finrank_range_synthesis row

example {k I J : Type*} [Field k] [Fintype I] [Fintype J]
    (row : J → I → k) :
    Module.finrank k
          (LinearMap.ker (RB31E2E.FiniteRowSystem.constraint row)) +
        Fintype.card J =
      Fintype.card I + RB31E2E.FiniteRowSystem.stressDim row :=
  RB31E2E.FiniteRowSystem.solutionDim_add_rowCard_eq_coordinateCard_add_stressDim row

example {k I J : Type*} [Field k] [Fintype I] [Fintype J]
    (row : J → I → k) :
    Module.finrank k (Submodule.span k (Set.range row)) +
        RB31E2E.FiniteRowSystem.stressDim row =
      Fintype.card J :=
  RB31E2E.FiniteRowSystem.finrank_span_add_stressDim_eq_card row

example {L K I J : Type*}
    [Field L] [Field K] [Algebra L K] [Finite J]
    (v : I → J → L) :
    Module.finrank L (Submodule.span L (Set.range v)) =
      Module.finrank K
        (Submodule.span K
          (Set.range (fun i ↦
            RB31E2E.FiniteFamilyBaseChange.mapVector (K := K) (v i)))) :=
  RB31E2E.FiniteFamilyBaseChange.finrank_span_range_mapVector v

example {L K I J : Type*}
    [Field L] [Field K] [Algebra L K] [Finite I] [Finite J]
    (v : I → J → L) :
    Module.finrank L (Submodule.span L (Set.range v)) =
      Module.finrank K
        (Submodule.span K
          (Set.range (fun i ↦
            RB31E2E.FiniteFamilyBaseChange.mapVector (K := K) (v i)))) :=
  RB31E2E.FiniteFamilyBaseChange.finrank_span_range_mapVector_finite v

noncomputable def blockMap
    {k X Z Y W : Type*} [Field k]
    [AddCommGroup X] [Module k X]
    [AddCommGroup Z] [Module k Z]
    [AddCommGroup Y] [Module k Y]
    [AddCommGroup W] [Module k W]
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    (X × Z) →ₗ[k] (Y × W) :=
  RB31E2E.BlockKernelExact.blockMap A B C

noncomputable def connectingMap
    {k X Z Y W : Type*} [Field k]
    [AddCommGroup X] [Module k X]
    [AddCommGroup Z] [Module k Z]
    [AddCommGroup Y] [Module k Y]
    [AddCommGroup W] [Module k W]
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    LinearMap.ker C →ₗ[k] (Y ⧸ LinearMap.range A) :=
  RB31E2E.BlockKernelExact.connectingMap A B C

example
    {k X Z Y W : Type*} [Field k]
    [AddCommGroup X] [Module k X]
    [AddCommGroup Z] [Module k Z]
    [AddCommGroup Y] [Module k Y]
    [AddCommGroup W] [Module k W]
    [FiniteDimensional k X] [FiniteDimensional k Z]
    (A : X →ₗ[k] Y) (B : Z →ₗ[k] Y) (C : Z →ₗ[k] W) :
    Module.finrank k
        (LinearMap.ker (RB31E2E.BlockKernelExact.blockMap A B C)) =
      Module.finrank k (LinearMap.ker A) +
        Module.finrank k
          (LinearMap.ker
            (RB31E2E.BlockKernelExact.connectingMap A B C)) :=
  RB31E2E.BlockKernelExact.finrank_blockKernel A B C

end PublicAPISmoke.Linear
