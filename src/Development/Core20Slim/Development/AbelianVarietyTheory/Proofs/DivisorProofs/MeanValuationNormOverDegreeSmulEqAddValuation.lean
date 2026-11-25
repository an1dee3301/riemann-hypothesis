module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH
public import Batteries.Logic
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas

@[expose] public section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum

theorem IsMinPol.scaleRoots_eq {K : Type} [Field K] {σ : K →+* ℂ} {β : ℂ} {u : K} {p q : K[X]}
    (hp : IsMinPol σ β p) (hq : IsMinPol σ (σ u * β) q) (hu : u ≠ 0) : q = p.scaleRoots u := by
  let := σ.toAlgebra
  have ep := hp.eq_minpoly
  have eq := hq.eq_minpoly
  have hr0 : (p.scaleRoots u).eval₂ σ (σ u * β) = 0 := scaleRoots_eval₂_eq_zero σ hp.2.2
  have hs0 : (q.scaleRoots u⁻¹).eval₂ σ β = 0 := by
    have := scaleRoots_eval₂_eq_zero σ (s := u⁻¹) hq.2.2
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul] at this
  have d1 : q ∣ p.scaleRoots u := by
    rw [eq]; exact minpoly.dvd K (σ u * β) hr0
  have d2 : p ∣ q.scaleRoots u⁻¹ := by
    rw [ep]; exact minpoly.dvd K β hs0
  have hq0 : q.scaleRoots u⁻¹ ≠ 0 := scaleRoots_ne_zero hq.1.ne_zero _
  have le1 : p.natDegree ≤ q.natDegree := by
    have := natDegree_le_of_dvd d2 hq0
    rwa [natDegree_scaleRoots] at this
  exact (eq_of_monic_of_dvd_of_natDegree_le hq.1 ((monic_scaleRoots_iff u).2 hp.1) d1
    (by rw [natDegree_scaleRoots]; exact le1)).symm

end GlobalTheory.FunObj.SqNum

theorem GlobalTheory.FunObj.SqNum.meanVal_vw_smul : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  intro K _ _ _ σ β u p q hp hq hβ hu w
  obtain ⟨hc, hd⟩ := hp.ne_zero hβ
  rw [hp.scaleRoots_eq hq hu]
  unfold GlobalTheory.FunObj.SqNum.meanVal_vw
  rw [natDegree_scaleRoots, coeff_scaleRoots, Nat.sub_zero]
  have hm : vw w (p.coeff 0 * u ^ p.natDegree) = vw w (p.coeff 0) + p.natDegree * vw w u := by
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hc)
        (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 (pow_ne_zero _ hu)),
      ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
  rw [hm]
  have : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
