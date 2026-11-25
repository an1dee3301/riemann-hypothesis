module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriod

theorem half_comb_not_mem (w₁ w₂ : ℂ) (hind : LinearIndependent ℝ ![w₁, w₂]) (a b : ℤ)
    (hab : ¬ (2 ∣ a ∧ 2 ∣ b)) :
    ((a : ℂ) * w₁ + (b : ℂ) * w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  intro h
  rw [AddSubgroup.mem_closure_pair] at h
  obtain ⟨m, n, hmn⟩ := h
  rw [LinearIndependent.pair_iff] at hind
  have key : ((a - 2 * m : ℤ) : ℝ) • w₁ + ((b - 2 * n : ℤ) : ℝ) • w₂ = 0 := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination (-2 : ℂ) * hmn
  obtain ⟨h1, h2⟩ := hind _ _ key
  have h1' : a - 2 * m = 0 := by exact_mod_cast h1
  have h2' : b - 2 * n = 0 := by exact_mod_cast h2
  exact hab ⟨⟨m, by omega⟩, ⟨n, by omega⟩⟩

theorem exists_other_half_period : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ,
    2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  rintro Λ ⟨w₁, w₂, hind, rfl⟩ P _ _
  have hw₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have hw₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have n₁ : w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 0 (by decide)
    simpa using this
  have n₂ : w₂ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 0 1 (by decide)
    simpa using this
  have n₃ : (w₁ - w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 (-1) (by decide)
    convert this using 2
    push_cast; ring
  by_cases hP : P - w₁ / 2 ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)
  · refine ⟨w₂ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₂, n₂, ?_⟩
    intro h
    apply n₃
    have := AddSubgroup.sub_mem _ h hP
    convert this using 1
    ring
  · exact ⟨w₁ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₁, n₁, hP⟩

end GlobalTheory.HalfPeriod
