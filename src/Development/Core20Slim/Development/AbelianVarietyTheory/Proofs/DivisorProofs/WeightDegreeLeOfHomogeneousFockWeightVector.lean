module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Prod
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm in
theorem degW_le_of_isSide {σ : Type} {p q r s : ℕ} {e : Ln p q r s → σ}
    {act : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} [Fintype σ]
    (he : Function.Bijective e) (h : IsSide e act) {d : ℕ}
    {μ : Ix p q → ℚ} {P : MvPolynomial σ ℂ} (hd : P ∈ homog σ d) (hP0 : P ≠ 0)
    (hP : P ∈ wtSub act μ) : degW (cPair r s) μ ≤ d := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hP0
  obtain ⟨h1, h2⟩ := (h.mem_wtSub μ P).1 hP
  have e1 : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hd (mem_support_iff.1 hm)
  rw [← e1, degree_eq_blocks he, degW, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum,
    Nat.cast_sum]
  refine add_le_add (Finset.sum_le_sum fun t _ => ?_) (Finset.sum_le_sum fun t _ => ?_)
  · rw [mixed_weight _ _ (h1 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])
  · rw [mixed_weight _ _ (h2 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])

theorem degW_le_of_homog_wtSub : ∀ (p q r s : ℕ),
    (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧
    (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := fun _ _ _ _ =>
  ⟨fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Function.bijective_id GlobalTheory.JointHarm.isSide_one hd h0 hP,
    fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Prod.swap_bijective GlobalTheory.JointHarm.isSide_two hd h0 hP⟩

end GlobalTheory.FockAlg
