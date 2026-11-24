module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.PhNormUnits
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
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
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Classical Filter Topology MvPowerSeries.WithPiTopology

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_var {σ : Type*} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X i

theorem const_phAt {τ : Type*} (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries τ ℂ_[p])
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (phAt ph a) = PowerSeries.constantCoeff ph := by

  unfold phAt
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [map_pow, ha, zero_pow hd, smul_zero]

section Lin2

variable (hE : CalcEquiv) (hSub : CalcSubst)
variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)

include hSub hex0 hinv in
theorem int_add (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x y : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hx : IntegralMv x) (hy : IntegralMv y) :
    IntegralMv (add l ex x y) := by

  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := by
    intro i
    fin_cases i <;> simp [hx0, hy0]
  have hsI : ∀ i, IntegralMv (![x, y] i) := by
    intro i
    fin_cases i <;> simp [hx, hy]
  have h1 := (hSub p (Fin 2) τ ![x, y] hs0 hsI).2 _ hIA
  rw [sb_add ![x, y] hs0 hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1), sb_X, sb_X] at h1
  · exact h1
  all_goals exact hs0

include hSub hex0 hinv in
theorem int_mulBy_of (c : ℂ_[p]) (hc : IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    {τ : Type} (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) :
    IntegralMv (mulBy l ex c x) := by

  have hs0 : ∀ i : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => x) i) = 0 := fun _ => hx0
  have hsI : ∀ i : Unit, IntegralMv ((fun _ : Unit => x) i) := fun _ => hx
  have h1 := (hSub p Unit τ (fun _ : Unit => x) hs0 hsI).2 _ hc
  rw [sb_mulBy (fun _ : Unit => x) hs0 hex0 hinv _ _ (constantCoeff_var ()), sb_X] at h1
  · exact h1
  all_goals exact hs0

include hSub hex0 hinv in
theorem int_mulBy_nat (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) (k : ℕ) :
    IntegralMv (mulBy l ex (k : ℂ_[p]) x) := by

  have hz : ∀ c, MvPowerSeries.constantCoeff (mulBy l ex c x) = 0 := by
    intro c
    unfold mulBy
    refine z0_pt_zero_pt_one_L3 hex0 _ ?_
    rw [map_mul, constantCoeff_subst_log hex0 hinv x hx0, mul_zero]
  induction k with
  | zero =>
    rw [Nat.cast_zero, mulBy_zero' hex0]
    intro n
    simp [IsIntP]
  | succ k ih =>
    rw [mulBy_succ hex0 hinv k x hx0]
    exact int_add hSub hex0 hinv hIA _ _ (hz _) hx0 ih hx

include hSub hex0 hinv in
theorem int_mulBy_zp (hC : CalcClosed) (hD : NatDense)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (x : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0) (hx : IntegralMv x) (n : ℤ_[p]) :
    IntegralMv (mulBy l ex (zc n) x) := by

  obtain ⟨u, hu⟩ := hD p n
  have hcont := cont_mulBy hex0 hinv x hx0
  have hconv : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (mulBy l ex ((u k : ℕ) : ℂ_[p]) x)) atTop
      (𝓝 (MvPowerSeries.coeff e (mulBy l ex (zc n) x))) :=
    fun e => tendsto_coeff_of_cont (fun c => mulBy l ex c x) hcont hu e
  exact (hC p τ _ _ hconv).2 (fun k => int_mulBy_nat hSub hex0 hinv hIA x hx0 hx (u k))

theorem ph_const_of {ph : PowerSeries ℂ_[p]}
    (h2 : Simeq (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (2 * 2) * phAt ph (Xv ()))) (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff ph = 0 := by

  have hm0 : MvPowerSeries.constantCoeff (mulBy l ex 2 (Xv () : MvPowerSeries Unit ℂ_[p])) = 0 := by
    unfold mulBy
    refine z0_pt_zero_pt_one_L3 hex0 _ ?_
    rw [map_mul, constantCoeff_subst_log hex0 hinv _ (constantCoeff_var ()), mul_zero]
  have hc1 : MvPowerSeries.constantCoeff (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.constantCoeff ph := const_phAt ph _ hm0
  have hc2 : MvPowerSeries.constantCoeff (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.constantCoeff ph := const_phAt ph _ (constantCoeff_var ())
  have hc3 : MvPowerSeries.constantCoeff (MvPowerSeries.C (2 * 2 : ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) = 2 * 2 :=
    MvPowerSeries.constantCoeff_C _
  have h1 := h2.1
  rw [map_sub, map_mul, hc1, hc2, hc3] at h1
  have h3 : (3 : ℂ_[p]) ≠ 0 := by norm_num
  have h4 : 3 * PowerSeries.constantCoeff ph = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h h3
  · exact h

include hex0 hinv in
theorem add_zero'' {τ : Type*} (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) :
    add l ex z 0 = z := by

  calc add l ex z 0 = add l ex (mulBy l ex 1 z) (mulBy l ex 0 z) := by
        rw [mulBy_one hex0 hinv z hz, mulBy_zero' hex0 z]
    _ = mulBy l ex (1 + 0) z := add_mulBy hex0 hinv 1 0 z hz
    _ = z := by rw [add_zero, mulBy_one hex0 hinv z hz]

include hex0 hinv in
theorem be_zero {τ : Type*} {ph : PowerSeries ℂ_[p]} (hph : PowerSeries.constantCoeff ph = 0)
    (z : MvPowerSeries τ ℂ_[p]) (hz : MvPowerSeries.constantCoeff z = 0) : be l ex ph z 0 = 0 := by

  unfold be
  rw [add_zero'' hex0 hinv z hz]
  unfold phAt
  rw [PowerSeries.subst_zero_of_constantCoeff_zero hph]
  ring

variable {ph : PowerSeries ℂ_[p]}
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))

include hSub hex0 hinv hB in
theorem be_add_left {τ : Type} (x y z : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hx : IntegralMv x) (hy : IntegralMv y) (hz : IntegralMv z) :
    Simeq (be l ex ph (add l ex x y) z) (be l ex ph x z + be l ex ph y z) := by

  have hs0 : ∀ i, MvPowerSeries.constantCoeff (![x, y, z] i) = 0 := by
    intro i
    fin_cases i <;> simp [hx0, hy0, hz0]
  have hsI : ∀ i, IntegralMv (![x, y, z] i) := by
    intro i
    fin_cases i <;> simp [hx, hy, hz]
  have hA01 : MvPowerSeries.constantCoeff (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    constantCoeff_formalAdd hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1)
  have h1 := (hSub p (Fin 3) τ ![x, y, z] hs0 hsI).1 _ _ hB
  rw [sb_be ![x, y, z] hs0 hex0 hinv ph _ _ hA01 (constantCoeff_var 2), sb_add ![x, y, z] hs0 hex0 hinv _ _ (constantCoeff_var 0) (constantCoeff_var 1),
    sb_add', sb_be ![x, y, z] hs0 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_var 2),
    sb_be ![x, y, z] hs0 hex0 hinv ph _ _ (constantCoeff_var 1) (constantCoeff_var 2), sb_X, sb_X, sb_X] at h1
  · exact h1
  all_goals first | exact hs0 | exact hex0 | exact hinv

include hSub hex0 hinv hB in
theorem be_add_right {τ : Type} (x y z : MvPowerSeries τ ℂ_[p]) (hx0 : MvPowerSeries.constantCoeff x = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hx : IntegralMv x) (hy : IntegralMv y) (hz : IntegralMv z) :
    Simeq (be l ex ph z (add l ex x y)) (be l ex ph z x + be l ex ph z y) := by

  have hsym : ∀ a b : MvPowerSeries τ ℂ_[p], be l ex ph a b = be l ex ph b a := by
    intro a b
    unfold be
    rw [add_comm']
    ring
  rw [hsym z (add l ex x y), hsym z x, hsym z y]
  exact be_add_left hSub hex0 hinv hB x y z hx0 hy0 hz0 hx hy hz

include hE hSub hex0 hinv hB in
theorem be_nat (hph : PowerSeries.constantCoeff ph = 0)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (z y : MvPowerSeries τ ℂ_[p]) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz : IntegralMv z) (hy : IntegralMv y) (k : ℕ) :
    Simeq (be l ex ph z (mulBy l ex (k : ℂ_[p]) y)) (MvPowerSeries.C (k : ℂ_[p]) * be l ex ph z y) := by

  induction k with
  | zero =>
    rw [Nat.cast_zero, mulBy_zero' hex0, be_zero hex0 hinv hph z hz0, map_zero, zero_mul]
    exact (hE p τ 0 0 0 0).1
  | succ k ih =>
    rw [mulBy_succ hex0 hinv k y hy0]
    have hmk0 : MvPowerSeries.constantCoeff (mulBy l ex (k : ℂ_[p]) y) = 0 := by
      unfold mulBy
      refine z0_pt_zero_pt_one_L3 hex0 _ ?_
      rw [map_mul, constantCoeff_subst_log hex0 hinv y hy0, mul_zero]
    have hmkI : IntegralMv (mulBy l ex (k : ℂ_[p]) y) := int_mulBy_nat hSub hex0 hinv hIA y hy0 hy k
    have h1 := be_add_right hSub hex0 hinv hB (mulBy l ex (k : ℂ_[p]) y) y z hmk0 hy0 hz0 hmkI hy hz
    have h2 := (hE p τ _ _ _ _).2.2.2.1 ih
      (hE p τ (be l ex ph z y) (be l ex ph z y) (be l ex ph z y) (be l ex ph z y)).1
    have h3 := (hE p τ _ _ _ 0).2.2.1 h1 h2
    have h4 : MvPowerSeries.C (k : ℂ_[p]) * be l ex ph z y + be l ex ph z y =
        MvPowerSeries.C ((k + 1 : ℕ) : ℂ_[p]) * be l ex ph z y := by
      rw [Nat.cast_succ, map_add (f := _), map_one]
      ring
    rw [← h4]
    exact h3

include hE hSub hex0 hinv hB in
theorem be_zp (hC : CalcClosed) (hD : NatDense) (hph : PowerSeries.constantCoeff ph = 0)
    (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) {τ : Type}
    (z y : MvPowerSeries τ ℂ_[p]) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (hy0 : MvPowerSeries.constantCoeff y = 0) (hz : IntegralMv z) (hy : IntegralMv y) (n : ℤ_[p]) :
    Simeq (be l ex ph z (mulBy l ex (zc n) y)) (MvPowerSeries.C (zc n) * be l ex ph z y) := by

  obtain ⟨u, hu⟩ := hD p n
  let F : ℂ_[p] → MvPowerSeries τ ℂ_[p] := fun c => be l ex ph z (mulBy l ex c y) - MvPowerSeries.C c * be l ex ph z y
  have hcont : Continuous F := by
    refine (cont_be hex0 hinv ph z y hz0 hy0).sub ?_
    refine continuous_pi (fun e => ?_)
    show Continuous (fun c : ℂ_[p] => MvPowerSeries.coeff e (MvPowerSeries.C c * be l ex ph z y))
    simp only [MvPowerSeries.coeff_C_mul]
    exact continuous_id.mul continuous_const
  have hconv : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F ((u k : ℕ) : ℂ_[p]))) atTop
      (𝓝 (MvPowerSeries.coeff e (F (zc n)))) :=
    fun e => tendsto_coeff_of_cont F hcont hu e
  have hk : ∀ k, Simeq (F ((u k : ℕ) : ℂ_[p])) 0 := fun k =>
    ((hE p τ _ _ 0 0).2.2.2.2.2).mp (be_nat hE hSub hex0 hinv hB hph hIA z y hz0 hy0 hz hy (u k))
  have h1 := (hC p τ (fun k => F ((u k : ℕ) : ℂ_[p])) (F (zc n)) hconv).1 hk
  exact ((hE p τ _ _ 0 0).2.2.2.2.2).mpr h1

end Lin2

end PI.PhNormUnits.UnitaryGroupMassFormula
