module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.BeConjNorm
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.Development
public import Development.Core20Slim.Formalism.PeriodIntegrals.PhNormUnits
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.SimeqSubst1
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Classical

namespace PI.BeConjNormW

open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula

variable {p : ℕ} [Fact p.Prime]

theorem coeff_one_subst (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 a := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 1 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 1)).trans (finsum_congr fun k => smul_eq_mul _ _)
  have hz : ∀ k, 2 ≤ k → PowerSeries.coeff 1 (a ^ k) = 0 := by
    intro k hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul, zero_add]
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hz k (by omega), mul_zero])

private theorem coeff_zero_subst_of_constantCoeff_eq_zero (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 0 f := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 0 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 0)).trans (finsum_congr fun k => smul_eq_mul _ _)
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 1)]
  · simp
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem linear_coeff_padic : LinCoeff := by
  intro q _ l ex hex hle c
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := coeff_zero_subst_of_constantCoeff_eq_zero ex l hex
    rw [hle, PowerSeries.coeff_zero_X, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  have hprod : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have h := coeff_one_subst ex l hex hl0
    rw [hle, PowerSeries.coeff_one_X] at h
    exact h.symm
  have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[q]) = 0 := PowerSeries.constantCoeff_X
  have hsX0 : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_subst_of_constantCoeff_eq_zero _ _ hX0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  have hsX1 : PowerSeries.coeff 1 (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) =
      PowerSeries.coeff 1 l := by
    rw [coeff_one_subst _ _ hX0 hl0, PowerSeries.coeff_one_X, mul_one]
  have hc0 : PowerSeries.constantCoeff
      (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [map_mul, hsX0, mul_zero]
  have key := coeff_one_subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex hc0 hex
  rw [PowerSeries.coeff_C_mul, hsX1] at key
  show PowerSeries.coeff 1 (PowerSeries.subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex : PowerSeries ℂ_[q]) = c
  rw [key]
  linear_combination c * hprod

theorem core_of (hI : IntInv) (hL : LinCoeff) : StepCore := by
  intro p _ l ex ph hl0 hex0 hinv hph S hswap hadd hintS hIA hnm hdec hnorm hB
  have hE := norm_units_equivalence
  have hSub := norm_units_substitution
  have hC := norm_units_closed_form
  have hD := natCast_dense_p_adic
  have z0 := constantCoeff_var (p := p) (0 : Fin 2)
  have z1 := constantCoeff_var (p := p) (1 : Fin 2)
  have hInv : ∀ c : ℂ_[p], ‖c‖ = 1 → IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (mulBy l ex c⁻¹ (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    intro c hc hcI
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hs0 : ∀ i : Unit, MvPowerSeries.constantCoeff
        ((fun _ => (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p])) i) = 0 :=
      fun _ => constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ())
    have hcomp := sb_mulBy (fun _ => (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p])) hs0 hex0 hinv c⁻¹
      (Xv ()) (constantCoeff_var ())
    rw [sb_X _ hs0] at hcomp
    rw [mulBy_mulBy hex0 hinv _ _ _ (constantCoeff_var ()), inv_mul_cancel₀ hc0, mulBy_one hex0 hinv _ (constantCoeff_var ())] at hcomp
    have key := hI p (mulBy l ex c (Xv ())) (mulBy l ex c⁻¹ (Xv ())) (constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ()))
      (constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ())) (by rw [hL p l ex hex0 hinv c]; exact hc) (fun n => hcI _) hcomp
    intro e
    have he : e = Finsupp.single () (e ()) := Finsupp.ext fun u => by cases u; simp
    unfold IsIntP
    rw [he]
    exact key (e ())
  have hU : ∀ β ∈ S, ‖β.1‖ = 1 → Simeq (be l ex ph (mulBy l ex β.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex β.2 (Xv 1))) := by
    intro β hβ h1
    obtain ⟨n, hn⟩ := hnm β hβ
    have hβ1 : β.1 ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    have hw : IntegralMv (mulBy l ex β.1⁻¹ (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) :=
      int_mulBy_of hSub hex0 hinv β.1⁻¹ (hInv β.1 h1 (hintS β hβ)) _ z1 (int_X 1)
    exact units_iv hE hSub hex0 hinv β.1 β.2 hβ1 hw
      (sTrans hE (units_i hE hSub hex0 hinv hIA _ _ (hnorm β hβ))
        (units_ii hE hSub hC hD hex0 hinv hph hIA hB _ _ n hn))
  intro α hα
  obtain ⟨β, hβ, γ, hγ, hb1, hg1, rfl⟩ := hdec α hα
  have iM : ∀ c, IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]) → ∀ i : Fin 2,
      IntegralMv (mulBy l ex c (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) :=
    fun c hc i => int_mulBy_of hSub hex0 hinv c hc _ (constantCoeff_var i) (int_X i)
  simp only [Prod.fst_add, Prod.snd_add]
  rw [← add_mulBy hex0 hinv _ _ _ z0, ← add_mulBy hex0 hinv _ _ _ z1]
  refine sTrans hE (be_add_left hSub hex0 hinv hB _ _ _ (constantCoeff_formalSMul hex0 hinv _ _ z0) (constantCoeff_formalSMul hex0 hinv _ _ z0)
    z1 (iM _ (hintS β hβ) 0) (iM _ (hintS γ hγ) 0) (int_X 1)) ?_
  refine sTrans hE (sAdd hE (hU β hβ hb1) (hU γ hγ hg1)) ?_
  exact sSymm hE (be_add_right hSub hex0 hinv hB _ _ _ (constantCoeff_formalSMul hex0 hinv _ _ z1) (constantCoeff_formalSMul hex0 hinv _ _ z1) z0
    (iM β.2 (hintS β.swap (hswap β hβ)) 1) (iM γ.2 (hintS γ.swap (hswap γ hγ)) 1) (int_X 0))

theorem beConjNorm_of_intInv (hI : IntInv) : PI.BeConjNorm.BeConjNorm :=
  beConjNorm_of (core_of hI linear_coeff_padic)

end PI.BeConjNormW
