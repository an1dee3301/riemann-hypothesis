module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector : ∀ (p q r s : ℕ), (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧ (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := by
  first | exact @GlobalTheory.FockAlg.degW_le_of_homog_wtSub | exact GlobalTheory.FockAlg.degW_le_of_homog_wtSub | (intros; apply GlobalTheory.FockAlg.degW_le_of_homog_wtSub <;> assumption)
