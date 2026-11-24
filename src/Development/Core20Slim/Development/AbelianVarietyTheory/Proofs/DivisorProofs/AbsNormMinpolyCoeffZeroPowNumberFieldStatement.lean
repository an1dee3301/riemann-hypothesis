module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberField
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Norm.Defs

@[expose] public section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → IsAlgebraic ℚ β → |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree = |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  first | exact @GlobalTheory.NormTower.abs_norm_coeff_zero_pow | exact GlobalTheory.NormTower.abs_norm_coeff_zero_pow | (intros; apply GlobalTheory.NormTower.abs_norm_coeff_zero_pow <;> assumption)
