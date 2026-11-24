module

public import Mathlib
public import Formalism.FormalGroupLog.Statement
public import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT 

variable {K : Type} [NormedField K] [IsUltrametricDist K]

section Ring
variable {ι : Type}

theorem integralMv_iff_divBy_one (F : MvPowerSeries ι K) : IntegralMv F ↔ DivByMv (1 : K) F := by
  first
  | exact Iff.rfl
  | (unfold IntegralMv DivByMv; simp)
  | simp [IntegralMv, DivByMv]
theorem divByMv_mul {x y : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv y G) :
    DivByMv (x * y) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul, norm_mul]
  refine Finset.sum_induction _ (fun z : K => ‖z‖ ≤ ‖x‖ * ‖y‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by rw [norm_zero]; positivity) ?_
  intro p _
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) (norm_nonneg _)
theorem integralMv_one : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
theorem integralMv_mul {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by
  rw [integralMv_iff_divBy_one] at *
  have h := divByMv_mul hF hG
  rwa [one_mul] at h
theorem integralMv_pow {F : MvPowerSeries ι K} (hF : IntegralMv F) (n : ℕ) : IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integralMv_one
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hF


end Ring

section OneVar






end OneVar

section Subst
variable {ι : Type}

private theorem norm_finsum_le_of_forall_norm_le {α : Type} (g : α → K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖g i‖ ≤ C) : ‖∑ᶠ i, g i‖ ≤ C := by
  by_cases hs : (Function.support g).Finite
  · rw [finsum_eq_sum g hs]
    exact Finset.sum_induction _ (fun z : K => ‖z‖ ≤ C)
      (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
      (by rw [norm_zero]; exact hC) (fun i _ => h i)
  · rw [finsum_of_infinite_support hs, norm_zero]
    exact hC


theorem divByMv_subst2 {x : K} {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : DivByMv x F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : DivByMv x (F.subst P) := by
  have ha : MvPowerSeries.HasSubst P := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hprod : ∀ e : Fin 2 →₀ ℕ, IntegralMv (e.prod fun s k => P s ^ k) := by
    intro e
    unfold Finsupp.prod
    exact Finset.prod_induction _ IntegralMv (fun _ _ => integralMv_mul) integralMv_one
      (fun s _ => integralMv_pow (hP s) _)
  intro d
  rw [MvPowerSeries.coeff_subst ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => by
    rw [smul_eq_mul, norm_mul]
    have h1 := (integralMv_iff_divBy_one _).mp (hprod e) d
    rw [norm_one] at h1
    calc ‖MvPowerSeries.coeff e F‖ * ‖MvPowerSeries.coeff d (e.prod fun s k => P s ^ k)‖
        ≤ ‖x‖ * 1 := mul_le_mul (hF e) h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _
theorem integralMv_subst2 {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : IntegralMv F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : IntegralMv (F.subst P) := by
  rw [integralMv_iff_divBy_one] at hF ⊢
  exact divByMv_subst2 hF hP0 hP

end Subst

section Frob
variable {l : ℕ} {σ : K →+* K} {ι : Type}



end Frob

end ReciprocityTheory.ChartRestriction.L1
