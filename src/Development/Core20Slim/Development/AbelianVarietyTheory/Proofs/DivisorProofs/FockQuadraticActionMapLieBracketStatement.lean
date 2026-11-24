module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracket
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockQuadraticAction_map_lie_bracket : ∀ (p q r s : ℕ) (Y Z : Matrix (Ln p q r s) (Ln p q r s) ℂ), omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y := by
  first | exact @GlobalTheory.FockLie.omAct_lie | exact GlobalTheory.FockLie.omAct_lie | (intros; apply GlobalTheory.FockLie.omAct_lie <;> assumption)
