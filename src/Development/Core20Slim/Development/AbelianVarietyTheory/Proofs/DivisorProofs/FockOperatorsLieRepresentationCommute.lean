module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracketStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
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

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem _root_.GlobalTheory.FockAlg.fock_lie_and_commute : ∀ (p q r s : ℕ),
    (∀ Y Z, _root_.Formalism.BasicNotions.TH.omAct p q r s (Y * Z - Z * Y) =
      _root_.Formalism.BasicNotions.TH.omAct p q r s Y * _root_.Formalism.BasicNotions.TH.omAct p q r s Z - _root_.Formalism.BasicNotions.TH.omAct p q r s Z * _root_.Formalism.BasicNotions.TH.omAct p q r s Y) ∧
    _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct1 p q r s) ∧ _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct2 p q r s) ∧
    ∀ Y Z, _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y * _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z = _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z * _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y :=
  fun p q r s => ⟨_root_.GlobalTheory.FockLie.omAct_lie p q r s,
    _root_.GlobalTheory.FockPair.pair_lie_commute p q r s⟩

end GlobalTheory.FockAlg
