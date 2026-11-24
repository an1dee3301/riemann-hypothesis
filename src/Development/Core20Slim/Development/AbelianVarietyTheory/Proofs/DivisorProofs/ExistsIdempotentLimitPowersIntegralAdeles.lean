module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open scoped Nat

namespace GlobalTheory.AlgIntIdem

theorem natCast_dvd_pow_sub {E : Type} [Field E] [NumberField E] (x : 𝓞 E) (N t : ℕ)
    (hN : 0 < N) (ht : 0 < t) :
    (N : 𝓞 E) ∣ x ^ ((N ^ Module.finrank ℤ (𝓞 E))! * t) - x ^ (N ^ Module.finrank ℤ (𝓞 E))! := by
  set I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    simp only [I, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ I) = N ^ Module.finrank ℤ (𝓞 E) := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      Ideal.absNorm_span_natCast]
  have h := GlobalTheory.IdealIdele.pow_factorial_mul (Ideal.Quotient.mk I x) t ht
  rw [hcard, ← map_pow, ← map_pow, Ideal.Quotient.eq] at h
  exact Ideal.mem_span_singleton.1 h

theorem idem : ∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w := by
  intro D x
  set d := Module.finrank ℤ (𝓞 D.host.E)
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  have hx : inc D (x : D.host.E) ∈ OhE D := VacMove.inc_int D x
  have key : ∀ N t : ℕ, 0 < N → 0 < t → ∃ w ∈ OhE D,
      inc D (x : D.host.E) ^ ((N ^ d)! * t) = inc D (x : D.host.E) ^ (N ^ d)! + (N : AE D) * w := by
    intro N t hN ht
    obtain ⟨w, hw, h⟩ := VacMove.inc_dvd D (natCast_dvd_pow_sub x N t hN ht)
    refine ⟨w, hw, ?_⟩
    rw [← h]
    push_cast
    rw [map_sub, map_pow, map_pow]
    ring
  obtain ⟨e, he, h⟩ := hcpl (fun N => inc D (x : D.host.E) ^ (N ^ d)!) (fun N => pow_mem hx _) (by
    intro N m hN hm
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial
      (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right N hm) d)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨w, hw, hh⟩ := key N t hN ht0
    exact ⟨w, hw, by simp only [ht, hh]⟩)
  refine ⟨e, he, ?_, fun N hN => ⟨(N ^ d)!, Nat.factorial_pos _, h N hN⟩⟩
  rw [← sub_eq_zero]
  refine hsep _ fun N hN => ?_
  obtain ⟨w, hw, hh⟩ := h N hN
  obtain ⟨c, hc, hc'⟩ := key N 2 hN two_pos
  refine ⟨c + (2 * inc D (x : D.host.E) ^ (N ^ d)! * w + N * w * w - w), ?_, ?_⟩
  · exact add_mem hc (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (pow_mem hx _)) hw)
      (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
  · rw [pow_mul] at hc'
    rw [hh]; linear_combination hc'

end GlobalTheory.AlgIntIdem
