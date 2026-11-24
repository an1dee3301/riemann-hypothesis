module

public import Mathlib
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
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
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Push

@[expose] public section

namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem injective_of_pderiv {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}
    (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (d : ι → Module.End ℂ V)
    (hd : ∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p))
    (h1 : Φ₀ 1 ≠ 0) : Function.Injective Φ₀ := by
  classical
  have hC : ∀ p : MvPolynomial ι ℂ, Φ₀ p = 0 → (∀ m ∈ p.support, m = 0) → p = 0 := by
    intro p hp hs
    have e : p = (p.coeff 0) • (1 : MvPolynomial ι ℂ) := by
      ext m
      by_cases hm : m = 0
      · subst hm; simp
      · have : p.coeff m = 0 := by
          by_contra h
          exact hm (hs m (mem_support_iff.2 h))
        rw [this, coeff_smul, coeff_one, if_neg (Ne.symm hm), smul_zero]
    rw [e, map_smul, smul_eq_zero] at hp
    rcases hp with hp | hp
    · rw [e, hp, zero_smul]
    · exact absurd hp h1
  have key : ∀ n : ℕ, ∀ p : MvPolynomial ι ℂ, (∀ m ∈ p.support, m.degree ≤ n) →
      Φ₀ p = 0 → p = 0 := by
    intro n
    induction n with
    | zero =>
      intro p hs hp
      exact hC p hp (fun m hm => (Finsupp.degree_eq_zero_iff m).1 (Nat.le_zero.1 (hs m hm)))
    | succ n ih =>
      intro p hs hp
      have hz : ∀ i, pderiv i p = 0 := by
        intro i
        apply ih
        · intro m hm
          rw [mem_support_iff, coeff_pderiv] at hm
          have h2 := hs _ (mem_support_iff.2 (left_ne_zero_of_mul hm))
          rw [map_add (f := _), Finsupp.degree_single] at h2
          omega
        · rw [hd, hp, map_zero]
      apply hC p hp
      intro m hm
      by_contra hm0
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra h
        push Not at h
        exact hm0 (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have hc := congrArg (fun q : MvPolynomial ι ℂ => q.coeff (m - Finsupp.single i 1)) (hz i)
      rw [coeff_pderiv, tsub_add_cancel_of_le hle, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_eq_zero] at hc
      rcases hc with hc | hc
      · exact (mem_support_iff.1 hm) hc
      · exact (Nat.cast_add_one_ne_zero _) hc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  exact key (p.support.sup fun m => m.degree) p
    (fun m hm => Finset.le_sup (f := fun m : ι →₀ ℕ => m.degree) hm) hp

end GlobalTheory.FockAlg
