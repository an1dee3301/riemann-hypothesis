module

public import Mathlib
public import Init.BinderNameHint
public import Init.Classical
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
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Variant₂.N1

open IsLocalRing

theorem exists_eq_unit_mul_pow_adicCompletion {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : AdicCompletion (maximalIdeal R) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (maximalIdeal R) R)ˣ),
      x = ↑u * (algebraMap R (AdicCompletion (maximalIdeal R) R)) ϖ ^ n := by

  have hM : maximalIdeal (AdicCompletion (maximalIdeal R) R) =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ} := by
    have e := congrArg (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      hϖ.maximalIdeal_eq
    rw [AdicCompletion.maximalIdeal_eq_map, e, Ideal.map_span, Set.image_singleton]
  have hMpow : ∀ k : ℕ, maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ ^ k} := fun k => by
    rw [hM, Ideal.span_singleton_pow]

  have hex : ∃ k : ℕ, x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k := by
    by_contra h
    push Not at h
    apply hx
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff
      (I := maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (M := AdicCompletion (maximalIdeal R) R)) x
    intro k
    simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero] using h k
  classical
  have hk : x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ Nat.find hex :=
    Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hk
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hxn : x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
    have := Nat.find_min hex (show n < Nat.find hex by omega)
    simpa using this
  rw [hMpow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hyu : IsUnit y := by
    rw [← notMem_maximalIdeal]
    intro hyM
    apply hk
    rw [hn, hMpow, Ideal.mem_span_singleton']
    rw [hM, Ideal.mem_span_singleton'] at hyM
    obtain ⟨z, hz⟩ := hyM
    exact ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩

end GroundTheory.Variant₂.N1
