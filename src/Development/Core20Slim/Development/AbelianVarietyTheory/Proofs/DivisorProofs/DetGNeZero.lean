module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

def rsub {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w

theorem rsub_X {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) (v : σ) :
    rsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _

variable {ι : Type}

open Classical in
def frameMat {d a : ℕ} (x₀ : Var ι d a → ℂ) : Matrix (ι × Fin a × Fin a) (Var ι d a) ℂ :=
  by
    classical
    exact fun w v => if w.1 = v.1 ∧ w.2.2 = v.2.2 then x₀ (v.1, v.2.1, w.2.1) else 0

def detG [Fintype ι] (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_detG [Fintype ι] (a : ℕ) (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (detG a n) = detChar n g := by
  unfold detG detChar
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem detG_ne_zero [Fintype ι] (a : ℕ) (n : ι → ℕ) : detG (ι := ι) a n ≠ 0 := by
  intro h
  have := eval_detG (ι := ι) a n (fun _ => 1)
  rw [h, map_zero] at this
  simp [detChar] at this

end GlobalTheory.MinorFrame
