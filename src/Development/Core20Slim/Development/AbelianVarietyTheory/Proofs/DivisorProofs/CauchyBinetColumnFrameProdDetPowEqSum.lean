module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormRowSubProdMinors
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs

@[expose] public section

open Classical MvPolynomial

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem eval_minorAt_frame {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (s : Fin a → Fin d) :
    eval x₀ (minorAt τ s) = ((Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i)).submatrix s id).det := by
  unfold minorAt
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem rsub_frame_X {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (i j : Fin a) :
    rsub (frameMat x₀)ᴴ (X (τ, i, j)) = ∑ r : Fin d, C (star (x₀ (τ, r, i))) * (X (τ, r, j) : Pol ι d a) := by
  rw [rsub_X, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [frameMat, Matrix.conjTranspose_apply]
    · intro b _ hb; simp [frameMat, Matrix.conjTranspose_apply, Ne.symm hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [frameMat, Matrix.conjTranspose_apply, Ne.symm hb]
  · simp

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem rsub_frame_det {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) :
    rsub (frameMat x₀)ᴴ ((Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det) =
      ∑ s : {s : Fin a → Fin d // StrictMono s}, C (star (eval x₀ (minorAt τ s.1))) * minorAt τ s.1 := by
  rw [AlgHom.map_det]
  set A : Matrix (Fin d) (Fin a) ℂ := Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i) with hA
  have hM : (rsub (frameMat x₀)ᴴ : MvPolynomial (ι × Fin a × Fin a) ℂ →ₐ[ℂ] Pol ι d a).mapMatrix
      (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)) =
      (Aᴴ.map (C : ℂ →+* Pol ι d a)) * xMat τ d a := by
    ext i j
    simp [rsub_frame_X, xMat, Matrix.mul_apply, hA, Matrix.conjTranspose_apply]
  rw [hM, det_mul_eq_sum_sm]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  · rw [eval_minorAt_frame, ← hA, Matrix.submatrix_map, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]
    exact (RingHom.map_det _ _).symm

theorem rsub_frame_detG {a d : ℕ} (n : ι → ℕ) (x₀ : Var ι d a → ℂ) :
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (eval x₀ (prodMinors T)) • prodMinors T := by
  unfold detG
  simp only [map_prod, map_pow, rsub_frame_det]
  rw [Finset.prod_congr rfl fun τ _ => (Fin.prod_const (n τ) _).symm]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold prodMinors
  simp only [map_prod, star_prod, smul_eq_C_mul, Finset.prod_mul_distrib]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

theorem rsub_frame_detG_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : Var ι d a → ℂ),
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (MvPolynomial.eval x₀ (prodMinors T)) • prodMinors T :=
  fun _ _ n x₀ => rsub_frame_detG n x₀

end GlobalTheory.MinorFrame
