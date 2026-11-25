module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoices
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_parameterSizes_testChoices : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  first | exact @GlobalTheory.KerConjMean.TopSizes.sizesK | exact GlobalTheory.KerConjMean.TopSizes.sizesK | (intros; apply GlobalTheory.KerConjMean.TopSizes.sizesK <;> assumption)
