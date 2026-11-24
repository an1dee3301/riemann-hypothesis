module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimirStatement
public import Batteries.Classes.RatCast
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.LowestType

theorem two_le_of_not_sameBlock {p q : ℕ} {a b : Ix p q} (h : ¬ sameBlock a b) : 2 ≤ p + q := by
  unfold sameBlock at h
  rcases a with i | i <;> rcases b with j | j
  · exact (h trivial).elim
  · have hi := i.pos
    have hj := j.pos
    omega
  · have hi := i.pos
    have hj := j.pos
    omega
  · exact (h trivial).elim

theorem gapGt_of_cube {p q : ℕ} {lam : Ix p q → ℚ} (hg : GapGt lam (((p + q : ℕ) : ℝ) ^ 3))
    {h : ℝ} (hh : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) → h ≤ ((p + q : ℕ) : ℝ) ^ 3) : GapGt lam h := by
  unfold GapGt at hg ⊢
  intro a b hab
  have h2 : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast two_le_of_not_sameBlock hab
  exact lt_of_le_of_lt (hh h2) (hg a b hab)

private lemma cube_div_add_one_le_cube_and_sub_one_le {n : ℝ} (h2 : 2 ≤ n) : n ^ 3 / 24 + 1 ≤ n ^ 3 ∧ n - 1 ≤ n ^ 3 := by

  have hp : 0 ≤ n * (n - 1) * (n + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have e : n * (n - 1) * (n + 1) = n ^ 3 - n := by ring
  constructor <;> linarith

theorem embeds_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3) → ∀ (A B : UGKMod p q) (u : A.M.V) (v : B.M.V), IsHW A.M.act (blattner lam) u → IsHW B.M.act (blattner lam) v → casimir A.M.act u = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • u → casimir B.M.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v → IrrGK B.M → ∃ e : B.M.V →ₗ[ℂ] A.M.V, Function.Injective e ∧ e v = u ∧ ∀ Z x, e (B.M.act Z x) = A.M.act Z (e x) := by
  intro hQ7 hQ8 p q lam hlam hgap A B u v hu hv hcu hcv hirr

  have g1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).1)
  have g2 : GapGt lam (((p + q : ℕ) : ℝ) - 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).2)
  obtain ⟨⟨e, he, hcomm, heu, -⟩, -⟩ :=
    GlobalTheory.T.highest_weight_iso_of_equal_casimir hQ7 hQ8 p q lam hlam g1 g2 A B u v hu hv hcu hcv hirr
  exact ⟨e, he, heu, hcomm⟩

end GlobalTheory.LowestType
