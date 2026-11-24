module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffPowMemS
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.RingTheory.MvPowerSeries.Basic
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

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem lamA_coeff_wser (wq : PowerSeries ℂ_[p]) (n : ℕ) :
    PowerSeries.coeff n (wser wq) = if 3 ≤ n then PowerSeries.coeff (n - 3) wq else 0 := by
  simp [wser, PowerSeries.coeff_X_pow_mul']

theorem lamA_coeff_lam (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam wq) = PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) := rfl

theorem lamA_single0 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem lamA_single1 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 1 (e 1) ↔ e 0 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem coeff_wSeriesVar_zero (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 0) = if e 1 = 0 then PowerSeries.coeff (e 0) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single0 e) rfl rfl

theorem coeff_wSeriesVar_one (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 1) = if e 0 = 0 then PowerSeries.coeff (e 1) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single1 e) rfl rfl

theorem lamA_coeff_mul_X (f : MvPowerSeries (Fin 2) ℂ_[p]) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * Xv i) =
      if 1 ≤ e i then MvPowerSeries.coeff (e - Finsupp.single i 1) f else 0 := by
  rw [Xv, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]

theorem lam_mul (wq : PowerSeries ℂ_[p]) :
    (Xv 1 - Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * lam wq = wv wq 1 - wv wq 0 := by
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm (Xv 1), mul_comm (Xv 0), lamA_coeff_mul_X, lamA_coeff_mul_X,
    coeff_wSeriesVar_zero, coeff_wSeriesVar_one, lamA_coeff_lam, lamA_coeff_lam]
  have a1 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 0 = e 0 := by simp
  have a2 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 1 = e 1 - 1 := by simp
  have a3 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 0 = e 0 - 1 := by simp
  have a4 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 1 = e 1 := by simp
  rw [a1, a2, a3, a4]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0
  · simp [h0, h1]
  · have : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    simp [h0, h1, this]
  · have : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h2 : e 0 - 1 + 0 + 1 = e 0 := by omega
    simp [h0, h1, this, h2]
  · have h3 : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h4 : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    have h2 : e 0 - 1 + e 1 + 1 = e 0 + (e 1 - 1) + 1 := by omega
    simp [h0, h1, h3, h4, h2]

theorem wv_line1 (wq : PowerSeries ℂ_[p]) : wv wq 1 = lam wq * Xv 1 + nu wq := by
  have h := lam_mul wq
  simp only [nu]
  linear_combination -h

theorem constantCoeff_lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lamA_coeff_lam, lamA_coeff_wser]
  simp

theorem lamA_wser_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S)
    (n : ℕ) : PowerSeries.coeff n (wser wq) ∈ S := by
  rw [lamA_coeff_wser]; split_ifs
  · exact hS _
  · exact S.zero_mem

theorem lam_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∀ e, MvPowerSeries.coeff e (lam wq) ∈ S := by
  intro e
  rw [lamA_coeff_lam]
  exact lamA_wser_mem hS _

theorem G_wv {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (i : Fin 2) :
    G W (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wv wq i) = 0 := by
  have hs : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.X i
  set φ := PowerSeries.substAlgHom (R := ℂ_[p]) hs with hφ
  have hX : (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = φ PowerSeries.X := by
    rw [hφ, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
  have hw : wv wq i = φ (wser wq) := by
    rw [hφ, PowerSeries.coe_substAlgHom]; rfl
  rw [hX, hw]
  have : G W (φ PowerSeries.X) (φ (wser wq)) = φ (G W PowerSeries.X (wser wq)) := by
    simp only [G, map_add (f := _), map_sub, map_mul, map_pow, AlgHom.commutes]
  rw [this, G_wser h, map_zero]

end PI.AddIntG.Wk
