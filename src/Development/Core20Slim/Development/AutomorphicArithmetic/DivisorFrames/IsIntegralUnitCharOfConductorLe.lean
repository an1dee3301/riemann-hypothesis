module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

private theorem UpperTheory.pow_sub_eq_one_of_condLE_valuation_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ)
    (hν : CondLE ϖ e ν) (x : kˣ) (hx : valuation k (x : k) = 1) (a b : ℕ) (hab : a < b)
    (h : valuation k ((x : k) ^ b - (x : k) ^ a) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    ν x ^ (b - a) = 1 := by
  have hmem : x ^ (b - a) ∈ unitCong (ϖ ^ e) := by
    show valuation k ((x ^ (b - a) : kˣ) : k) = 1 ∧
      valuation k (((x ^ (b - a) : kˣ) : k) - 1) ≤ valuation k ((ϖ ^ e : kˣ) : k)
    have hfac : (x : k) ^ b - (x : k) ^ a = (x : k) ^ a * ((x : k) ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    rw [hfac, map_mul, map_pow, hx, one_pow, one_mul] at h
    refine ⟨?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
    · rw [Units.val_pow_eq_pow_val]
      exact h
  rw [← map_pow]
  exact hν _ hmem

theorem UpperTheory.isIntegral_unitChar_of_conductor_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ), IsUnif ϖ → CondLE ϖ e ν → ∀ x : kˣ, valuation k (x : k) = 1 → IsIntegral ℤ (ν x : ℂ) := by
  intro k _ _ _ _ ϖ e ν hϖ hν x hx
  have hpow : ∀ n : ℕ, (x : k) ^ n ∈ 𝒪[k] := fun n =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_pow, hx, one_pow])
  let g : ℕ → Res (k := k) e := fun n => Ideal.Quotient.mk _ ⟨(x : k) ^ n, hpow n⟩
  obtain ⟨i, j, hne, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have key : ∀ a b : ℕ, a < b → g a = g b → IsIntegral ℤ (ν x : ℂ) := by
    intro a b hab h
    have h1 := Ideal.Quotient.eq.1 h.symm
    have h2 := (Model.val_le_iff_mem hϖ e _).1 h1
    have h3 : ν x ^ (b - a) = 1 := UpperTheory.pow_sub_eq_one_of_condLE_valuation_le ϖ e ν hν x hx a b hab (by simpa using h2)
    refine IsIntegral.of_pow (Nat.sub_pos_of_lt hab) ?_
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    exact isIntegral_one
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hg
  · exact key j i h hg.symm
