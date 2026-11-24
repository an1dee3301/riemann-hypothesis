module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormProportionalOfIrreducible
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_mul_of_finrank_hwSub_eq_one : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (E₁ : M.V →ₗ[ℂ] H₁) (E₂ : M.V →ₗ[ℂ] H₂), IrrGK M → Module.finrank ℂ ↥(hwSub M.act Λ) = 1 → Function.Injective E₁ → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₁ y) = inner ℂ (E₁ x) (E₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₂ (M.act Z x)) (E₂ y) = inner ℂ (E₂ x) (E₂ (M.act (adjZ Z) y))) → ∃ c : ℝ, ∀ y, ‖E₂ y‖ = c * ‖E₁ y‖ := by
  first | exact @GlobalTheory.FockTensor.norm_proportional_of_irreducible | exact GlobalTheory.FockTensor.norm_proportional_of_irreducible | (intros; apply GlobalTheory.FockTensor.norm_proportional_of_irreducible <;> assumption)
