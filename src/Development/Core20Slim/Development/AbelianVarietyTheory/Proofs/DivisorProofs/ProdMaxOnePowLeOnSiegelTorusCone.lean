module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConeMax

theorem prod_max_le_prod (r m e : ℕ) (c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c,
    ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤
      C * ∏ i, t i ^ e := by
  set c0 : ℝ := min c 1 ^ r with hc0
  have hm0 : 0 < min c 1 := lt_min hc one_pos
  have hc0pos : 0 < c0 := pow_pos hm0 r
  have hc0le : c0 ≤ 1 := pow_le_one₀ hm0.le (min_le_right _ _)
  refine ⟨(c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r, by positivity, ?_⟩
  intro t ht
  have hlow : ∀ i, c0 ≤ t i := fun i => GlobalTheory.LatCount.cone_pow_le hc ht i
  have htpos : ∀ i, 0 < t i := fun i => hc0pos.trans_le (hlow i)
  have h1 : ∀ i, max 1 (t i) ≤ t i * c0⁻¹ := by
    intro i
    have hi : 1 ≤ c0⁻¹ := one_le_inv₀ hc0pos |>.2 hc0le
    refine max_le ?_ ?_
    · rw [← mul_inv_cancel₀ hc0pos.ne']
      exact mul_le_mul_of_nonneg_right (hlow i) (inv_nonneg.2 hc0pos.le)
    · exact le_mul_of_one_le_right (htpos i).le hi
  have h2 : ∀ i, max 1 (t i)⁻¹ ≤ c0⁻¹ := by
    intro i
    refine max_le (one_le_inv₀ hc0pos |>.2 hc0le) ?_
    exact inv_anti₀ hc0pos (hlow i)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, max_self, one_pow, Finset.prod_const_one, mul_one]
  have A : ∏ i : Fin r, max 1 (t i) ^ e ≤ ∏ i : Fin r, (t i ^ e * c0⁻¹ ^ e) := by
    refine Finset.prod_le_prod₀ (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (le_max_left _ _ |>.trans' zero_le_one) (h1 i) e
  have B : ∏ i : Fin r, max 1 (t i)⁻¹ ^ e ≤ ∏ _i : Fin r, c0⁻¹ ^ e :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ =>
      pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (h2 i) e
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at A
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at B
  have hA0 : 0 ≤ ∏ i : Fin r, max 1 (t i)⁻¹ ^ e := Finset.prod_nonneg fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  calc (∏ i : Fin r, max 1 (t i) ^ e) * ∏ i : Fin r, max 1 (t i)⁻¹ ^ e
      ≤ ((∏ i : Fin r, t i ^ e) * (c0⁻¹ ^ e) ^ r) * (c0⁻¹ ^ e) ^ r :=
        mul_le_mul A B hA0
          (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (htpos i).le _) (by positivity))
    _ = (c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r * ∏ i, t i ^ e := by ring

end GlobalTheory.ConeMax
