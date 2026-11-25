module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKType
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType : ∀ (D : D7) (C : ℝ) (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank), (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  first | exact @GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | exact GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | (intros; apply GlobalTheory.RowReal.hw_basePar_eq_neg_lowK <;> assumption)
