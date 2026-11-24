module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadRowWeights
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Prelude

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_row_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ lam : ∀ j : Fin (S.m + 1), DomWeight (S.nR j), (∀ i, (lam 0).w i = hw Q.psiPar i) ∧ (∀ i, (lam (Fin.last _)).w i = hw Q.bigPar i) ∧ ∀ j : Fin S.m, StepW (Q.e j - (S.nR j.succ / 2 : ℕ)) (-Q.e j + (S.nR j.castSucc / 2 : ℕ)) (lam j.castSucc) (lam j.succ) := by
  first | exact @GlobalTheory.OneFunctional.RowWeights.exists_row_weights | exact GlobalTheory.OneFunctional.RowWeights.exists_row_weights | (intros; apply GlobalTheory.OneFunctional.RowWeights.exists_row_weights <;> assumption)
