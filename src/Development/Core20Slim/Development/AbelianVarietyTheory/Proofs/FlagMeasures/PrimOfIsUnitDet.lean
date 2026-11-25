module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.GramCount

variable {A : Type} [CommRing A]




variable (c : A →+* A) {n : ℕ}


















theorem card_fixed_sq (hc : ∀ u, c (c u) = u) {ω : A} (hω : IsUnit (ω - c ω))
    {M : Type} [AddCommGroup M] [Module A M] (σ : M →+ M) (hσ : ∀ x, σ (σ x) = x)
    (hs : ∀ (a : A) x, σ (a • x) = c a • σ x) :
    Nat.card {x : M // σ x = x} ^ 2 = Nat.card M ∧
      Nat.card {x : M // σ x = -x} ^ 2 = Nat.card M := by

  obtain ⟨U, hU⟩ := hω
  have h1 : (ω - c ω) * ↑U⁻¹ = 1 := by rw [← hU]; exact U.mul_inv
  have h2 : (c ω - ω) * c ↑U⁻¹ = 1 := by
    have h3 := congrArg c h1
    rwa [map_mul, map_sub, hc, map_one] at h3
  have hvn : c ↑U⁻¹ = -(↑U⁻¹ : A) := by
    linear_combination (-(c ↑U⁻¹)) * h1 + (-(↑U⁻¹ : A)) * h2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : A, (ω - c ω) * v = 1 ∧ c v = -v := ⟨_, h1, hvn⟩
  have hu : c (ω - c ω) = -(ω - c ω) := by
    rw [map_sub, hc]
    ring
  have hg : ∀ x, σ (v • (x - σ x)) = v • (x - σ x) := by
    intro x
    rw [hs, map_sub, hσ, hv2, neg_smul, ← smul_neg, neg_sub]
  have hab : ω * v = c ω * v + 1 := by linear_combination hv1
  have hf : ∀ x, σ (x - ω • v • (x - σ x)) = x - ω • v • (x - σ x) := by
    intro x
    rw [map_sub, hs, hg, smul_smul, smul_smul, hab, add_smul, one_smul]
    abel
  have e : M ≃ {x : M // σ x = x} × {x : M // σ x = x} :=
    { toFun := fun x => (⟨x - ω • v • (x - σ x), hf x⟩, ⟨v • (x - σ x), hg x⟩)
      invFun := fun p => p.1.1 + ω • p.2.1
      left_inv := fun x => sub_add_cancel _ _
      right_inv := fun p => by
        obtain ⟨⟨f, hf0⟩, ⟨g, hg0⟩⟩ := p
        have key : v • (f + ω • g - σ (f + ω • g)) = g := by
          rw [map_add (f := _), hs, hf0, hg0, add_sub_add_left_eq_sub, ← sub_smul, smul_smul, mul_comm,
            hv1, one_smul]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show f + ω • g - ω • v • (f + ω • g - σ (f + ω • g)) = f
          rw [key, add_sub_cancel_right]
        · exact key }
  have e2 : {x : M // σ x = -x} ≃ {x : M // σ x = x} :=
    { toFun := fun x => ⟨v • x.1, by rw [hs, x.2, hv2, smul_neg, neg_smul, neg_neg]⟩
      invFun := fun y => ⟨(ω - c ω) • y.1, by rw [hs, y.2, hu, neg_smul]⟩
      left_inv := fun x => Subtype.ext (by
        show (ω - c ω) • v • x.1 = x.1
        rw [smul_smul, hv1, one_smul])
      right_inv := fun y => Subtype.ext (by
        show v • (ω - c ω) • y.1 = y.1
        rw [smul_smul, mul_comm, hv1, one_smul]) }
  have hM : Nat.card M = Nat.card {x : M // σ x = x} ^ 2 := by
    rw [Nat.card_congr e, Nat.card_prod, sq]
  exact ⟨hM.symm, by rw [Nat.card_congr e2, hM]⟩

end GlobalTheory.GramCount
