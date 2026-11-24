module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_not_mem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [valuation_of_mk'] at ht
  set n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hn
  have hvb : v.intValuation b = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hb0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < v.intValuation b := by
    rw [hvb]; exact WithZero.exp_pos
  have hva : v.intValuation a ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hvb]; exact (div_le_one₀ hpos).1 ht
  have haI : a ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem a n).1 hva
  have hbI : b ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem b n).1 hvb.le
  have hbI' : b ∉ v.asIdeal ^ (n + 1) := by
    intro h
    have := (v.intValuation_le_pow_iff_mem b (n + 1)).2 h
    rw [hvb] at this
    have h2 := WithZero.exp_le_exp.1 this
    push_cast at h2
    omega
  have hdvd : v.asIdeal ^ n ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbI)
  obtain ⟨B', hB'⟩ := hdvd
  have hB'p : ¬ B' ≤ v.asIdeal := by
    intro hle
    apply hbI'
    have : Ideal.span {b} ≤ v.asIdeal ^ (n + 1) := by
      rw [hB', pow_succ]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self b)
  obtain ⟨s, hsB, hsp⟩ := Set.not_subset.1 hB'p
  refine ⟨s, hsp, ?_⟩
  have hmem : a * s ∈ Ideal.span {b} := by
    rw [hB']; exact Ideal.mul_mem_mul haI hsB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨r, ?_⟩
  show algebraMap R K s * IsLocalization.mk' K a ⟨b, hb⟩ = algebraMap R K r
  rw [IsFractionRing.mk'_eq_div]
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K), (IsFractionRing.injective R K).eq_iff]; exact hb0
  rw [mul_div_assoc', div_eq_iff hbK, ← map_mul, ← map_mul, hr, mul_comm a s]

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal



end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal



end GlobalTheory.InvDiffLocal
