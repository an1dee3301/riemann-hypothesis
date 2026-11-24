module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Prod
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_dualPair_swap_symmetry : ∀ (p q r s : ℕ), (∀ (Z : Mat p q) (P : Pol p q r s), rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P)) ∧ (∀ (Z : Mat r s) (P : Pol p q r s), rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P)) ∧ (∀ P : Pol p q r s, (P ∈ harm1 p q r s ↔ rename Prod.swap P ∈ harm2 r s p q) ∧ (P ∈ harm2 p q r s ↔ rename Prod.swap P ∈ harm1 r s p q)) := by
  first | exact @GlobalTheory.FockSwap.swap_symmetry | exact GlobalTheory.FockSwap.swap_symmetry | (intros; apply GlobalTheory.FockSwap.swap_symmetry <;> assumption)
