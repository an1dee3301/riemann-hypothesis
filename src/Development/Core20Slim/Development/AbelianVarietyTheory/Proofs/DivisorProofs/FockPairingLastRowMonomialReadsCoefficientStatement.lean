module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficient
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPairing_lastRow_monomial_reads_coefficient : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  first | exact @GlobalTheory.BrCoefFock.fockB_zmon_emb | exact GlobalTheory.BrCoefFock.fockB_zmon_emb | (intros; apply GlobalTheory.BrCoefFock.fockB_zmon_emb <;> assumption)
