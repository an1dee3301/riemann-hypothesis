module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order

@[expose] public section

open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.Ydb5.le_order_iff {σ R : Type*} [CommRing R]
    (f g : MvPowerSeries σ R) (n : ℕ) :
    (n : ℕ∞) ≤ (f - g).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    have h0 : coeff d (f - g) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    rwa [map_sub, sub_eq_zero] at h0
  · intro h
    refine nat_le_order fun d hd => ?_
    rw [map_sub, h d hd, sub_self]

theorem UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint.{u_1, u_2} :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] (Φ : MvPowerSeries σ R → MvPowerSeries σ R),
      (∀ (f g : MvPowerSeries σ R) (n : ℕ), (↑n : ℕ∞) ≤ (f - g).order → (↑(n + (1 : ℕ)) : ℕ∞) ≤ (Φ f - Φ g).order) →
        ∃! f : MvPowerSeries σ R, Φ f = f := by
  intro σ R _ Φ h
  simp only [UpperTheory.Reformulated.B.Ydb5.le_order_iff] at h
  have step : ∀ (k : ℕ) (g : MvPowerSeries σ R) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d (Φ^[k] g) = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k g
    induction k with
    | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h _ _ k ih
  let f : MvPowerSeries σ R := fun d => MvPowerSeries.coeff d (Φ^[d.degree + 1] 0)
  have hf : ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[d.degree + 1] 0) := fun _ => rfl
  have approx : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree < k →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d (Φ^[k] 0) := by
    intro k d hd
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
    rw [hf, Function.iterate_add_apply Φ (Nat.succ _) m]
    exact (step _ _ d (Nat.lt_succ_self _)).symm
  refine ⟨f, ?_, ?_⟩
  · ext d
    rw [h f _ d.degree (approx _) d (Nat.lt_succ_self _), hf, Function.iterate_succ_apply']
  · intro g hg
    ext d
    rw [hf, ← step _ g d (Nat.lt_succ_self _), Function.iterate_fixed hg]
