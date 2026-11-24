module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimir
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
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
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_iso_of_equal_casimir : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  first | exact @GlobalTheory.LowGen.gen_iso_of_lowest_type | exact GlobalTheory.LowGen.gen_iso_of_lowest_type | (intros; apply GlobalTheory.LowGen.gen_iso_of_lowest_type <;> assumption)
