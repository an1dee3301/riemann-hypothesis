module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {m n : ℕ}

theorem evX_Qb (ε : Fin m → Bool) (b : Bool) (i j : Fin n) (u : Fin m → Fin n → ℂ) :
    evX (Qb ε b i j) u = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [evX, Qb, map_sum]

theorem gramB_apply (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramB ε b u i j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := evX_Qb ε b i j u

theorem gramB_not (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB (fun a => !ε a) b u = gramB ε (!b) u := by
  ext i j
  simp only [gramB_apply]
  refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
  cases ε a <;> cases b <;> simp

theorem gramX_eq (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) :
    gramX ε u = gramB ε true u - gramB ε false u := by
  ext i j
  simp [gramX, gramB, Qp, evX, map_sub]

private theorem gramB_eq_conjTranspose_diagonal_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB ε b u = (Matrix.of u)ᴴ * diagonal (fun a => if ε a = b then (1 : ℂ) else 0) * Matrix.of u := by
  ext i j
  simp [gramB_apply, Matrix.mul_apply, diagonal_apply, Finset.sum_filter, conjTranspose_apply]

theorem gramB_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    gramB ε b (Matrix.of u * a) = aᴴ * gramB ε b u * a := by
  rw [gramB_eq_conjTranspose_diagonal_mul ε b u]
  refine (gramB_eq_conjTranspose_diagonal_mul ε b (Matrix.of u * a)).trans ?_
  change (Matrix.of u * a)ᴴ * _ * (Matrix.of u * a) = _
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem epsT_pos {t : ℝ} (ht : 0 < t) (ε : Fin m → Bool) : epsT t ε = ε := by
  funext a; simp [epsT, ht]

theorem epsT_nonpos {t : ℝ} (ht : ¬ 0 < t) (ε : Fin m → Bool) : epsT t ε = fun a => !ε a := by
  funext a; simp [epsT, ht]

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  simp only [cnt]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simpa using this

theorem chN_mul_gZf (ε : Fin m → Bool) {t c : ℝ} (htc : |t| = c) (b Z : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (u : Fin m → Fin n → ℂ) : chN ε t b u * gZf ε t c Z u = gZf ε t c (Z + b) u := by
  unfold chN gZf
  rw [← Complex.exp_add]
  congr 1
  rw [gramX_eq, conjTranspose_add, hb]
  by_cases ht : 0 < t
  · rw [epsT_pos ht]
    have htc' : t = c := by rw [← htc, abs_of_pos ht]
    subst htc'
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  · rw [epsT_nonpos ht, gramB_not, gramB_not]
    have htc' : t = -c := by rw [← htc, abs_of_nonpos (not_lt.mp ht), neg_neg]
    subst htc'
    simp only [Bool.not_true, Bool.not_false, Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.ofReal_neg]
    ring

theorem trace_cyc (Z a G : Matrix (Fin n) (Fin n) ℂ) : (Z * (aᴴ * G * a)).trace = (a * Z * aᴴ * G).trace := by
  rw [show Z * (aᴴ * G * a) = (Z * aᴴ * G) * a by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem gZf_mul (ε : Fin m → Bool) (t c : ℝ) (Z a : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) :
    gZf ε t c Z (Matrix.of u * a) = gZf ε t c (a * Z * aᴴ) u := by
  unfold gZf
  rw [gramB_mul, gramB_mul, trace_cyc, trace_cyc, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob.GaussH
