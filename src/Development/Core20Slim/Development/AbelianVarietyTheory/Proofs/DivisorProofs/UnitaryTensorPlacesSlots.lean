module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

open Matrix
open scoped Classical

namespace GlobalTheory

theorem pi_prod_rows_orthonormal {K : Type} [Fintype K] [DecidableEq K] {κ : K → Type}
    [∀ k, Fintype (κ k)] [∀ k, DecidableEq (κ k)] [DecidableEq (∀ k, κ k)]
    (A : ∀ k, Matrix (κ k) (κ k) ℂ)
    (hA : ∀ k a b, ∑ y, A k a y * star (A k b y) = if a = b then 1 else 0)
    (T T'' : ∀ k, κ k) :
    ∑ x : ∀ k, κ k, (∏ k, A k (T k) (x k)) * star (∏ k, A k (T'' k) (x k)) =
      if T = T'' then 1 else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k y => A k (T k) y * star (A k (T'' k) y))]
  rw [Finset.prod_congr rfl (fun k _ => hA k (T k) (T'' k)), Finset.prod_boole]
  by_cases hT : T = T''
  · subst hT; simp
  · rw [if_neg hT, if_neg]
    intro hall
    exact hT (funext fun k => hall k (Finset.mem_univ k))

theorem unitary_tensor_places_positions : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι]
    [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) →
    (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈
      Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  intro J ι _ _ _ _ n C hC
  have hC' : ∀ j (a b : ι), ∑ y, C j a y * star (C j b y) = if a = b then 1 else 0 := by
    intro j a b
    have := congrFun (congrFun ((mem_unitaryGroup_iff).1 (hC j)) a) b
    simpa only [Matrix.mul_apply, star_apply, Matrix.one_apply] using this
  have hD : ∀ j (S S'' : Fin (n j) → ι),
      ∑ y : Fin (n j) → ι, (∏ r, C j (S r) (y r)) * star (∏ r, C j (S'' r) (y r)) =
        if S = S'' then 1 else 0 := fun j =>
    pi_prod_rows_orthonormal (κ := fun _ => ι) (fun _ => C j) (fun _ => hC' j)
  have key := pi_prod_rows_orthonormal (κ := fun j => Fin (n j) → ι)
    (fun j => of fun S S' : Fin (n j) → ι => ∏ r, C j (S r) (S' r))
    (fun j a b => by simpa only [of_apply] using hD j a b)
  rw [mem_unitaryGroup_iff]
  ext T T''
  simpa only [Matrix.mul_apply, star_apply, of_apply, Matrix.one_apply] using key T T''

end GlobalTheory
