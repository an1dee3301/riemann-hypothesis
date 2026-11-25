module

public import Mathlib
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Variant₂.N1

theorem exists_pow_apply_eq_self_of_aeval_eq_zero {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (σ : Gal(Ω/K)) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hmem : ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet Ω := fun n => by
    rw [Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_algHom_apply, hx, map_zero]
  have : Finite (p.rootSet Ω) := (Polynomial.rootSet_finite p Ω).to_subtype
  let f : ℕ → p.rootSet Ω := fun n => ⟨(σ ^ n) x, hmem n⟩
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨j - i, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ i).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]
  · refine ⟨i - j, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ j).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]

end GroundTheory.Variant₂.N1
