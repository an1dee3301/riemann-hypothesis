module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_of_same_harishChandraParam_unitary : ∀ (k : ℕ) (u : Fin k → ℝ) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁)) (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), Formalism.MainNotions.S.IsHCTypeU k u π₁ → Formalism.MainNotions.S.IsHCTypeU k u π₂ → ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  first | exact @GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | exact GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU <;> assumption)
