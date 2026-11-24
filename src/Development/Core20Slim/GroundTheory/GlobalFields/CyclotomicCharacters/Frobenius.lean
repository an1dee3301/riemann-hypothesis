module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Nat.Div.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IsGaloisGroup.Defs
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open NumberField

namespace GroundTheory.Global

namespace Cyclotomic

section Frobenius

variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]

variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]


include hp in
theorem ne_bot_of_liesOver : P ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
    (by simpa using hp.out.ne_zero) P


include hp in
theorem finite_quotient : Finite (𝓞 K ⧸ P) :=
  have : NeZero P := ⟨ne_bot_of_liesOver p K P⟩
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne P)


omit hp [NumberField K] [P.IsPrime] in
theorem card_quotient_under : Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}),
    Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]


omit [NeZero m] hp [NumberField K] [IsCyclotomicExtension {m} ℚ K] [P.IsPrime] in
theorem natCast_notMem_of_not_dvd (hm : ¬ p ∣ m) : ((m : ℕ) : 𝓞 K) ∉ P := by
  intro h
  have : ((m : ℤ)) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using h
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at this
  exact hm (Int.natCast_dvd_natCast.mp this)

theorem eq_of_forall_pow_eq_one {σ τ : Gal(K/ℚ)}
    (h : ∀ x : K, x ^ m = 1 → σ x = τ x) : σ = τ := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ K
  apply (IsCyclotomicExtension.Rat.galEquivZMod m K).injective
  have h₁ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K σ hζ.pow_eq_one
  have h₂ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K τ hζ.pow_eq_one
  rw [h _ hζ.pow_eq_one, h₂] at h₁
  rw [Units.ext_iff]
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h₁.symm)


omit hp [IsCyclotomicExtension {m} ℚ K] [P.IsPrime] in
theorem IsArithFrobAt.apply_of_pow_eq_one (hm : ¬ p ∣ m) {σ : Gal(K/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) {x : K} (hx : x ^ m = 1) : σ x = x ^ p := by
  have hxi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne m), ?_⟩
    simp [hx]
  let y : 𝓞 K := ⟨x, hxi⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    exact hx
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hy
    (natCast_notMem_of_not_dvd p K P hm)
  rw [card_quotient_under p K P] at h
  exact congrArg (fun z : 𝓞 K => (z : K)) h

theorem isArithFrobAt_iff (hm : ¬ p ∣ m) (σ : Gal(K/ℚ)) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : K, x ^ m = 1 → σ x = x ^ p := by
  refine ⟨fun hσ x hx => IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx, fun h => ?_⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  have : σ = τ := eq_of_forall_pow_eq_one (m := m) K fun x hx => by
    rw [h x hx, IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]
  rwa [this]

theorem existsUnique_isArithFrobAt (hm : ¬ p ∣ m) : ∃! σ : Gal(K/ℚ), IsArithFrobAt ℤ σ P := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  refine ⟨τ, hτ, fun σ hσ => eq_of_forall_pow_eq_one (m := m) K fun x hx => ?_⟩
  rw [IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx,
    IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]

end Frobenius

end Cyclotomic

end GroundTheory.Global
