module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcCH

open DCalcH DCalcBH

variable {m n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [h]

theorem det_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j))).det = Complex.exp (-(z * ∑ j, (X j : ℂ))) := by
  rw [det_diagonal, ← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem zpow_exp_neg (w : ℂ) (p : ℕ) : Complex.exp (-w) ^ (-(p : ℤ)) = Complex.exp ((p : ℂ) * w) := by
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem jC_one (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    jC e p q 1 X z = Complex.exp (((p : ℂ) + q) * (z * ∑ j, (X j : ℂ))) := by
  unfold jC
  simp only [mR_one, Matrix.one_mul]
  rw [det_aC]
  unfold aC
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, _root_.one_zpow, one_mul]
  rw [det_diag_exp, zpow_exp_neg, zpow_exp_neg, ← Complex.exp_add]
  congr 1
  ring

theorem inv_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j)))⁻¹ = diagonal fun j => Complex.exp (z * X j) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  conv_rhs => rw [← diagonal_one]
  congr 1
  funext j
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem ptZ_one (X : Fin n → ℝ) (z s₀ : ℂ) :
    ptZ 1 X z s₀ = s₀ • diagonal fun j => Complex.exp (2 * z * X j) := by
  unfold ptZ
  simp only [mR_one, Matrix.one_mul]
  unfold aC
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.zero_mul, zero_add, add_zero]
  rw [inv_diag_exp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_diagonal]
  congr 2
  funext j
  rw [← Complex.exp_add]
  congr 1
  ring

theorem gramB_diag (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramB ε b u j j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a j) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramB, Qb, evX, map_sum, eval_X]

theorem trace_sdiag (s₀ : ℂ) (w : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    ((s₀ • diagonal w) * G).trace = s₀ * ∑ j, w j * G j j := by
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  simp [trace, diagonal_mul]

theorem famC_one (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    famC ε t c e 1 X (s : ℂ) u = fF c X 1 u s := by
  unfold famC fF fP
  rw [jC_one, ptZ_one, ptZ_one, gs_vS]
  unfold gC
  rw [trace_sdiag, trace_sdiag]
  simp only [gramB_diag, evX_eq, map_one, one_mul]
  have hpq : ((cnt (epsT t ε) true : ℂ) + (cnt (epsT t ε) false : ℂ)) = (m : ℂ) := by
    rw [← Nat.cast_add, cnt_add]
  rw [hpq, ← Complex.exp_add, Complex.ofReal_exp]
  have hsum : ∀ j, (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) +
      (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
      (p := fun a => epsT t ε a = true) (f := fun a => star (u a j) * u a j)
    simp only [Bool.not_eq_true] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  have e2 : ∀ j, Complex.exp (2 * (s : ℂ) * (X j : ℂ)) = ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) := by
    intro j
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold nS
  push_cast
  simp only [e2]
  have key : Complex.I * (c : ℂ) * (Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) -
      Complex.I * (c : ℂ) * (-Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      -((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [← hsum, mul_add, Finset.sum_add_distrib]
    linear_combination ((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j +
      (c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) * hI
  rw [key, ← Complex.exp_add]
  have hswap : ∀ (E : Fin n → ℂ) (N : Fin m → Fin n → ℂ), (∑ j, E j * ∑ a, N a j) = ∑ a, ∑ j, N a j * E j := by
    intro E N
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  congr 1
  push_cast
  rw [hswap]
  ring

end DCalcCH

end PositivityTheory.Rg.Sw.Glob
