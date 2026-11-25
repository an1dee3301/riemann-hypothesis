module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardWeightSetGridEqGridRowSpaceRank
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Data.Finset.Card

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_weightSet_grid_eq_gridRowSpaceRank : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ((GlobalTheory.Grid.grid D τ).weightX j).card = GlobalTheory.Grid.rkX D j := by
  first | exact @GlobalTheory.Grid.card_weightX_grid | exact GlobalTheory.Grid.card_weightX_grid | (intros; apply GlobalTheory.Grid.card_weightX_grid <;> assumption)
