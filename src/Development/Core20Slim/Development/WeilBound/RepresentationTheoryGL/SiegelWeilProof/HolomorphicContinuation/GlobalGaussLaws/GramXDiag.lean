module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfInG
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussScalar
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS

variable {m n : ℕ}

def sigR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sigR ε a : ℝ) : ℂ) := by
  unfold sgn sigR
  by_cases h : ε a <;> simp [h]

theorem ftLoc_eq (ε : Fin m → Bool) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s f u = ftG (sigR ε) s f u := by
  simp only [ftLoc, ftG]
  congr 1
  funext y
  have key : ((of u)ᴴ * diagonal (sgn ε) * of y).trace.re =
      ∑ a, ∑ j, sigR ε a * ((starRingEnd ℂ) (u a j) * y a j).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sgn_eq, mul_comm (star (u a j)) _, mul_assoc, Complex.re_ofReal_mul]
    rfl
  rw [key]

theorem gramX_diag (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramX ε u j j = ∑ a, ((sigR ε a : ℝ) : ℂ) * ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, if_true,
    Bool.false_eq_true, if_false, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a <;> simp [h, sigR, Complex.conj_mul']

theorem chN_DG (ε : Fin m → Bool) (t : ℝ) (β : Fin n → ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (u : Fin m → Fin n → ℂ) :
    chN ε t (diagonal fun j => (β j : ℂ)) u * DG K γ u =
      DG K (fun a j => γ a j - I * t * (sigR ε a : ℂ) * (β j : ℂ)) u := by
  simp only [chN, DG]
  simp only [← Complex.exp_sum]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  have htr : (diagonal (fun j => (β j : ℂ)) * gramX ε u).trace = ∑ j, (β j : ℂ) * gramX ε u j j := by
    simp [Matrix.trace, Matrix.diagonal_mul]
  rw [htr]
  simp_rw [gramX_diag, Finset.mul_sum]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dg_const (K γ0 : ℂ) (v : Fin m → Fin n → ℂ) :
    DG K (fun _ _ => γ0) v = K * cexp (-γ0 * ∑ a, ∑ j, ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [DG]
  congr 1
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]

theorem vac_eq (ε : Fin m → Bool) (t c : ℝ) : vac (n := n) ε t c = DG 1 (fun _ _ => (c : ℂ)) := by
  funext y
  rw [dg_const, one_mul]
  simp only [vac, gZf]
  congr 1
  have hsum : (gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace =
      ∑ a, ∑ j, ((‖y a j‖ ^ 2 : ℝ) : ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, gramB, Qb, evX, map_sum, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : epsT t ε a <;> simp [h, Complex.conj_mul']
  rw [smul_mul_assoc, one_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    smul_mul_assoc, one_mul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_I]
  linear_combination ((c : ℂ) * ((gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace)) *
    Complex.I_sq + (-(c : ℂ)) * hsum

theorem levF_diag (e : ℤ) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j) (K : ℂ) (γ : Fin m → Fin n → ℂ) :
    levF e (diagonal fun j => (δ j : ℂ)) (DG K γ) =
      DG (K * (∏ j, (δ j : ℂ)) ^ m) (fun a j => γ a j * ((δ j : ℂ) ^ 2)) := by
  funext u
  simp only [levF, DG, Matrix.det_diagonal]
  have hD : (∏ j, (δ j : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (hδ j).ne'
  have hs : star (∏ j, (δ j : ℂ)) = ∏ j, (δ j : ℂ) := by
    rw [← Complex.ofReal_prod]
    exact Complex.conj_ofReal _
  rw [hs, ← zpow_add₀ hD, add_sub_cancel, zpow_natCast]
  rw [← mul_assoc, mul_comm (_ ^ m) K]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [Matrix.mul_diagonal, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.VacC
