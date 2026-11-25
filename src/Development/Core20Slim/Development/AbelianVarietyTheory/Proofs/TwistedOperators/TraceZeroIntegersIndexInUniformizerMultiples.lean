module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
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
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hq := traceZeroIndex_of_intIndex intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, h4, -, -, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖO : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0 := fun y => Iff.rfl
  have hinj : ∀ e : ℕ, Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) := fun e =>
    mul_right_injective₀ (pow_ne_zero e h0)
  have hmap : ∀ e : ℕ, (traceZero σ (ϖ ^ e)).map (AddMonoidHom.mulLeft (ϖ ^ e)) = T := fun e => by
    ext x
    rw [AddSubgroup.mem_map, memT]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_traceZero] at hy
      refine ⟨hy.1, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
      linear_combination ϖ ^ e * hy.2
    · rintro ⟨hx, hx0⟩
      refine ⟨(ϖ ^ e)⁻¹ * x, ?_, ?_⟩
      · rw [mem_traceZero, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
        refine ⟨hx, ?_⟩
        rw [map_mul, map_inv₀, map_pow, hϖ]
        linear_combination (ϖ ^ e)⁻¹ * hx0
      · rw [AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
  have h1 : traceZero σ 1 = T := by
    ext x
    rw [mem_traceZero, memT, one_mul]
  have hmulle : ∀ e : ℕ, T.map (AddMonoidHom.mulLeft (ϖ ^ e)) ≤ T := by
    rintro e _ ⟨y, hy, rfl⟩
    have hy : y ∈ T := hy
    rw [memT] at hy ⊢
    refine ⟨(intL L).mul_mem (pow_mem hϖO e) hy.1, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
    linear_combination ϖ ^ e * hy.2
  rw [← AddSubgroup.relIndex_map_map_of_injective (traceZero σ 1) (traceZero σ (ϖ ^ f)) (hinj f), hmap f, h1]
  induction f with
  | zero =>
    have : T.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = T := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hcomp : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (T.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ (hinj e)]
      exact hq
    have hle1 : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ T.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (by simpa using hmulle 1)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 (hmulle e), hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.InertZeta

end
