module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.PhNormUnits
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
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
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
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
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Monoid
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

section Calc

variable (hE : CalcEquiv)
include hE

theorem sRefl {σ : Type} (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := (hE p σ f f f f).1

theorem sOfEq {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : f = g) : Simeq f g := h ▸ sRefl hE f

theorem sSymm {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f :=
  (hE p σ f g f f).2.1 h

theorem sTrans {σ : Type} {f g k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g k) : Simeq f k :=
  (hE p σ f g k f).2.2.1 h1 h2

theorem sAdd {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f + h) (g + k) := (hE p σ f g h k).2.2.2.1 h1 h2

theorem sNeg {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) : Simeq (-f) (-g) :=
  (hE p σ f g f f).2.2.2.2.1 h1

theorem sSub {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f - h) (g - k) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact sAdd hE h1 (sNeg hE h2)

end Calc

theorem int_X {σ : Type*} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem coeff_subst_sum {τ : Type*} (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) =
      ∑ d ∈ Finset.range (e.degree + 1), PowerSeries.coeff d f • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hd
  rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simp [ha]) (by omega),
    smul_zero]

theorem cont_subst {τ : Type*} (G : ℂ_[p] → MvPowerSeries τ ℂ_[p])
    (hG : Continuous G) (h0 : ∀ x, MvPowerSeries.constantCoeff (G x) = 0) (f : PowerSeries ℂ_[p]) :
    Continuous fun x => (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p]) := by
  refine continuous_pi fun e => ?_
  change Continuous fun x => MvPowerSeries.coeff e (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p])
  simp_rw [coeff_subst_sum _ (h0 _), smul_eq_mul]
  refine continuous_finsetSum _ fun d _ => continuous_const.mul ?_
  exact (continuous_coeff ℂ_[p] e).comp (hG.pow d)

theorem tendsto_coeff_of_cont {τ : Type*} (F : ℂ_[p] → MvPowerSeries τ ℂ_[p]) (hF : Continuous F)
    {u : ℕ → ℂ_[p]} {c : ℂ_[p]} (hu : Tendsto u atTop (𝓝 c)) (e : τ →₀ ℕ) :
    Tendsto (fun k => MvPowerSeries.coeff e (F (u k))) atTop (𝓝 (MvPowerSeries.coeff e (F c))) :=
  (((continuous_coeff ℂ_[p] e).comp hF).tendsto c).comp hu

section Lin

variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)

include hex0 hinv

theorem cont_mulBy {τ : Type*} (y : MvPowerSeries τ ℂ_[p]) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => mulBy l ex c y :=
  cont_subst (fun c => MvPowerSeries.C c * PowerSeries.subst y l) (continuous_C.mul continuous_const)
    (fun c => by rw [map_mul, constantCoeff_subst_log hex0 hinv y hy, mul_zero]) ex

theorem cont_be {τ : Type*} (ph : PowerSeries ℂ_[p]) (z y : MvPowerSeries τ ℂ_[p])
    (hz : MvPowerSeries.constantCoeff z = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => be l ex ph z (mulBy l ex c y) := by
  have hA : Continuous fun c : ℂ_[p] => add l ex z (mulBy l ex c y) := by
    have : (fun c : ℂ_[p] => add l ex z (mulBy l ex c y)) = fun c =>
        PowerSeries.subst (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) ex := by
      funext c; unfold add; rw [L_mulBy hex0 hinv c y hy]
    rw [this]
    exact cont_subst (fun c : ℂ_[p] => PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l)
      (continuous_const.add (continuous_C.mul continuous_const))
      (fun c => by
        show MvPowerSeries.constantCoeff (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) = 0
        rw [map_add (f := _), map_mul, constantCoeff_subst_log hex0 hinv y hy, constantCoeff_subst_log hex0 hinv z hz]; simp) ex
  unfold be
  refine ((cont_subst _ hA (fun c => constantCoeff_formalAdd hex0 hinv _ _ hz (constantCoeff_formalSMul hex0 hinv c y hy)) ph).sub
    continuous_const).sub ?_
  exact cont_subst _ (cont_mulBy hex0 hinv y hy) (fun c => constantCoeff_formalSMul hex0 hinv c y hy) ph

end Lin

end PI.PhNormUnits.UnitaryGroupMassFormula
