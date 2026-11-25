module

public import Mathlib
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.CompanionTheory.SplitQuadratic

theorem isPrincipalIdealRing_of_sq_eq_sq :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
      (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) →
      (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ ι δ e hδ hspan _ he h2
  obtain ⟨e', he'⟩ := he.exists_right_inv
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hee' : ι e * ι e' = 1 := by rw [← map_mul, he', map_one]
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι hh
    rwa [map_mul, map_one, map_ofNat] at this
  have hδ' : δ * δ = ι e * ι e := by rw [hδ, map_mul]

  have hu2 : (ι e' * δ) * (ι e' * δ) = 1 := by
    linear_combination (ι e' * ι e') * hδ' + (ι e * ι e' + 1) * hee'

  set ε₁ : O := ι h * (1 + ι e' * δ) with hε₁
  set ε₂ : O := ι h * (1 - ι e' * δ) with hε₂
  have h11 : ε₁ * ε₁ = ε₁ := by
    rw [hε₁]
    linear_combination (ι h * (1 + ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h22 : ε₂ * ε₂ = ε₂ := by
    rw [hε₂]
    linear_combination (ι h * (1 - ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h12 : ε₁ * ε₂ = 0 := by
    rw [hε₁, hε₂]
    linear_combination (-(ι h * ι h)) * hu2
  have hsum : ε₁ + ε₂ = 1 := by
    rw [hε₁, hε₂]
    linear_combination h2'

  let φ : R × R →+* O :=
    { toFun := fun x => ι x.1 * ε₁ + ι x.2 * ε₂
      map_one' := by
        simp only [Prod.fst_one, Prod.snd_one, map_one, one_mul]
        exact hsum
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(ι x.1 * ι y.1)) * h11 + (-(ι x.2 * ι y.2)) * h22 +
          (-(ι x.1 * ι y.2 + ι x.2 * ι y.1)) * h12
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        ring }
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p, q, rfl⟩ := hspan y
    refine ⟨(p + q * e, p - q * e), ?_⟩
    show ι (p + q * e) * ε₁ + ι (p - q * e) * ε₂ = ι p + ι q * δ
    rw [hε₁, hε₂]
    simp only [map_add (f := _), map_sub, map_mul]
    linear_combination (ι p + ι q * ι e * ι e' * δ) * h2' + (ι q * δ) * hee'
  exact IsPrincipalIdealRing.of_surjective φ hsurj

end GlobalTheory.CompanionTheory.SplitQuadratic
