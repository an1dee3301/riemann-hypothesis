module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open scoped ComplexOrder in
theorem det_ne_zero_of_add_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (h : P + Pᴴ = (2 : ℂ) • (1 : Matrix n n ℂ)) : P.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0

  have hquad : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 2 * (star v ⬝ᵥ v) := by
    rw [h]
    first
      | simp [smul_mulVec, dotProduct_smul, smul_eq_mul]
      | simp [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
      | simp [dotProduct_smul, smul_eq_mul]

  have hzero : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 0 := by
    have hstar : star v ᵥ* Pᴴ = star (P *ᵥ v) := (star_mulVec P v).symm
    rw [add_mulVec, dotProduct_add, dotProduct_mulVec (star v) Pᴴ v, hstar, hv]
    simp
  have hnorm : star v ⬝ᵥ v = 0 := by
    have h2 : (2 : ℂ) * (star v ⬝ᵥ v) = 0 := hquad.symm.trans hzero
    rcases mul_eq_zero.mp h2 with h2 | h2
    · norm_num at h2
    · exact h2
  exact dotProduct_star_self_eq_zero.mp hnorm

private lemma isLeft_ne_of_posIx_eq {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) (h1 : posIx y.1 = posIx x.1)
    (h2 : posIx y.2 = posIx x.2) : x.1.isLeft ≠ y.1.isLeft := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases x1 with i | i <;> rcases x2 with j | j <;> rcases y1 with k | k <;> rcases y2 with l | l <;>
    simp_all [sameBlock, posIx, Fin.ext_iff]

private lemma eigP_add_star_eigP_eq_zero {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) : eigP x y + star (eigP y x) = 0 := by
  unfold eigP
  rw [if_neg hne, if_neg (Ne.symm hne)]
  by_cases h : posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2
  · have c1 : ¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2 := ⟨hy, h⟩
    have c2 : ¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2 :=
      ⟨hx, h.1.symm, h.2.symm⟩
    rw [if_pos c1, if_pos c2]
    have hL := isLeft_ne_of_posIx_eq x y hx hy hne h.1 h.2
    generalize x.1.isLeft = s at hL ⊢
    generalize y.1.isLeft = t at hL ⊢
    cases s <;> cases t <;> simp at hL ⊢
  · have c1 : ¬ (¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2) :=
      fun h' => h ⟨h'.2.1, h'.2.2⟩
    have c2 : ¬ (¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2) :=
      fun h' => h ⟨h'.2.1.symm, h'.2.2.symm⟩
    rw [if_neg c1, if_neg c2]
    simp

theorem eigenvectorMatrix_add_star {p q : ℕ} (ab cd : PIx p q) :
    eigP ab.1 cd.1 + star (eigP cd.1 ab.1) = if cd = ab then 2 else 0 := by
  by_cases hc : cd = ab
  · subst hc
    rw [if_pos rfl]
    norm_num [eigP]
  · rw [if_neg hc]
    exact eigP_add_star_eigP_eq_zero ab.1 cd.1 ab.2 cd.2 (fun h => hc (Subtype.ext h))

theorem det_eigenvectorMatrix_ne_zero :
    ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  intro p q
  apply det_ne_zero_of_add_conjTranspose
  ext cd ab
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [eigenvectorMatrix_add_star]
  split_ifs <;> norm_num

end GlobalTheory.PolarU
