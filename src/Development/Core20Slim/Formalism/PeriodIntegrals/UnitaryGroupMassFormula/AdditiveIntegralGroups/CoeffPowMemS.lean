module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
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
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
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

theorem wq_const {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  simp only [IsWq] at h
  have h1 := congrArg PowerSeries.constantCoeff h
  simpa using h1

theorem coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega

theorem coeff_pow_memS {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (k : ℕ) : ∀ i ≤ m, PowerSeries.coeff i (f ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ k ih =>
    intro i hi
    rw [pow_succ]
    exact coeff_mul_memS (fun j hj => ih j (hj.trans hi)) (fun j hj => hf j (hj.trans hi))

theorem coeff_termS (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by
  rw [mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

theorem wq_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, PowerSeries.coeff n wq ∈ S := by
  have t1 : ∀ (a : ℂ_[p]) (f : PowerSeries ℂ_[p]) (n : ℕ),
      PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * f) =
        if 1 ≤ n then a * PowerSeries.coeff (n - 1) f else 0 := by
    intro a f n
    rw [← coeff_termS, pow_one]
  simp only [IsWq] at h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    rw [hc]
    simp only [map_add (f := _), t1, coeff_termS, PowerSeries.coeff_one]
    refine S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h1 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h2 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)
      · exact S.zero_mem

theorem G_wser {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    G W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = 0 := by
  simp only [IsWq] at h
  unfold G wser
  rw [sub_eq_zero]
  conv_rhs => rw [h]
  ring

end PI.AddIntG.Wk
