module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqOfIrreducible
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalRingCardinality.DataTheta
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
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_eq_of_irrGK_of_inner_hw_eq : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y))) → Function.Injective j₂ → IrrGK M → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → Module.finrank ℂ ↥(hwSub M.act μ) = 1 → inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v) → ∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  first | exact @GlobalTheory.InvFormUnique.inner_eq_of_irreducible | exact GlobalTheory.InvFormUnique.inner_eq_of_irreducible | (intros; apply GlobalTheory.InvFormUnique.inner_eq_of_irreducible <;> assumption)
