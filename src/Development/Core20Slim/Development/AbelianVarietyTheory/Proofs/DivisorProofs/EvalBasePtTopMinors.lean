module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
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
public import Mathlib.Data.Prod.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RowIrr

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def basePt (ι : Type) (d a : ℕ) : Var ι d a → ℂ := fun y => if (y.2.1 : ℕ) = (y.2.2 : ℕ) then 1 else 0

def lowScal (d a : ℕ) (t : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else t

def topRows {a d : ℕ} (h : a ≤ d) : {s : Fin a → Fin d // StrictMono s} :=
  ⟨Fin.castLE h, Fin.strictMono_castLE h⟩

def topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : Pol ι d a :=
  prodMinors (ι := ι) (n := n) (fun _ _ => topRows h)

theorem eval_rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (rowSub κ P) = eval (fun y => ∑ i' : Fin d, κ y.1 i' y.2.1 * z (y.1, i', y.2.2)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rowSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp => simp [rowSub, hp] at *

theorem eval_colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (colSub g P) = eval (fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * z (y.1, y.2.1, j')) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp => simp [colSub, hp] at *

theorem rowSub_rowSub {d a : ℕ} (κ κ' : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rowSub κ (rowSub κ' P) = rowSub (fun τ => κ τ * κ' τ) P := by
  have : (rowSub κ).comp (rowSub κ') = (rowSub (fun τ => κ τ * κ' τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul, C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_one {d a : ℕ} (P : Pol ι d a) : rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) P = P := by
  have : (rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [rowSub, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single y.2.1]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem eval_basePt_topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : eval (basePt ι d a) (topMinors h n) = 1 := by
  simp only [topMinors, prodMinors, minorAt, map_prod, RingHom.map_det]
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => ?_
  have : (RingHom.mapMatrix (eval (basePt ι d a)))
      (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = 1 := by
    ext i i'
    simp [basePt, topRows, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

theorem topMinors_ne_zero {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : topMinors (ι := ι) h n ≠ 0 := by
  intro h0
  have := eval_basePt_topMinors (ι := ι) h n
  rw [h0, map_zero] at this
  exact zero_ne_one this

end GlobalTheory.MinorFrame.RowIrr
