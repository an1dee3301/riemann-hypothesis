module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

namespace NearUnitaryExp

open scoped Matrix.Norms.Frobenius


variable {n : ℕ}

theorem sqrt_hs_eq_norm (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow, hs]
  simp only [Real.rpow_two]

theorem hs_nonneg' (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_eq_hs (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = hs A := by
  rw [← sqrt_hs_eq_norm, Real.sq_sqrt (hs_nonneg' A)]

private lemma re_star_mul_self_eq_norm_sq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem hs_eq_re_trace (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    re_star_mul_self_eq_norm_sq]
  exact Finset.sum_comm







end NearUnitaryExp

end GlobalTheory
