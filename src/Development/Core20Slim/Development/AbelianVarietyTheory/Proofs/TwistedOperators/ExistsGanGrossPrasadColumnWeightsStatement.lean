module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadColumnWeights
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
theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_column_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧ (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧ ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (kap i.castSucc) (kap i.succ) := by
  first | exact @GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | exact GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | (intros; apply GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights <;> assumption)
