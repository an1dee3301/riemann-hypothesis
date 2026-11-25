module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.BiaddOfCube
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
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

namespace PI.BiaddOfCubeWork

open PI.BiaddOfCube

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_log_eq_zero {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hex'
  have h1 := PowerSeries.constantCoeff_subst (R := ℂ_[p]) hs l
  rw [h, finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero]),
    pow_zero, map_one, smul_eq_mul, mul_one] at h1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1]
  exact PowerSeries.constantCoeff_X

variable {σ : Type*}

theorem subst_subst_log {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X)
    (y : MvPowerSeries σ ℂ_[p]) (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hex')
    (PowerSeries.HasSubst.of_constantCoeff_zero hy), h,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hy)]

theorem constantCoeff_subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem add_comm' (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) :
    add l ex a b = add l ex b a := by
  show PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex =
    PowerSeries.subst (PowerSeries.subst b l + PowerSeries.subst a l) ex
  rw [add_comm]

theorem add_assoc' {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X)
    (a b c : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (hc : MvPowerSeries.constantCoeff c = 0) :
    add l ex (add l ex a b) c = add l ex a (add l ex b c) := by
  have hl := constantCoeff_log_eq_zero hex h
  have hla := constantCoeff_subst_zero hl a ha
  have hlb := constantCoeff_subst_zero hl b hb
  have hlc := constantCoeff_subst_zero hl c hc
  show PowerSeries.subst (PowerSeries.subst (add l ex a b) l + PowerSeries.subst c l) ex =
    PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst (add l ex b c) l) ex
  rw [show add l ex a b = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex from rfl,
    subst_subst_log hex h _ (by rw [map_add (f := _), hla, hlb, add_zero]),
    show add l ex b c = PowerSeries.subst (PowerSeries.subst b l + PowerSeries.subst c l) ex from rfl,
    subst_subst_log hex h _ (by rw [map_add (f := _), hlb, hlc, add_zero]), add_assoc]

theorem simeq_of_sub_eq {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (hs : Simeq f' g') : Simeq f g := by
  show MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
  rw [e]
  exact hs

theorem cc_Xv (i : Fin 3) : MvPowerSeries.constantCoeff (Xv (p := p) i) = 0 := by
  exact MvPowerSeries.constantCoeff_X i

end PI.BiaddOfCubeWork
