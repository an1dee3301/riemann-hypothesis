module

public import Mathlib
public import Init.BinderNameHint
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Push
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory.DetDerivativeAtOne

open Equiv Finset

theorem hasDerivAt_det_of_one {n : Type} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A (0 : ℝ) = (1 : Matrix n n ℂ))
    (hd : ∀ (i j : n), HasDerivAt (fun (t : ℝ) ↦ A t i j) (A' i j) (0 : ℝ)) :
    HasDerivAt (fun (t : ℝ) ↦ Matrix.det (A t)) (Matrix.trace A') (0 : ℝ) := by
  have hfun : (fun t : ℝ ↦ Matrix.det (A t)) =
      fun t ↦ ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i :=
    funext fun t ↦ Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ : Perm n, HasDerivAt (fun t : ℝ ↦ ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 :=
    fun σ ↦ HasDerivAt.fun_finsetProd (fun i _ ↦ hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm n)))
    (fun σ _ ↦ (hσ σ).const_mul ((Perm.sign σ : ℤ) : ℂ))
  refine hsum.congr_deriv (Eq.symm ?_)
  rw [h0]
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [Matrix.trace, Perm.one_apply, Matrix.one_apply]
  · intro σ _ hσ1
    have hz : ∀ i, (∏ j ∈ univ.erase i, (1 : Matrix n n ℂ) (σ j) j) = 0 := by
      intro i
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hc
        push Not at hc
        exact hσ1 (Equiv.ext hc)
      by_cases hki : k = i
      · subst hki
        apply Finset.prod_eq_zero (i := σ k)
        · simp [hk]
        · have : σ (σ k) ≠ σ k := fun h ↦ hk (σ.injective h)
          simp [Matrix.one_apply_ne this]
      · apply Finset.prod_eq_zero (i := k)
        · simp [hki]
        · simp [Matrix.one_apply_ne hk]
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.DetDerivativeAtOne
