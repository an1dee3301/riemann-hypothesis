module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBoundBottomPairsNormsGrid
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.ArchimedeanLeaf.LeafARCHFree
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanBound_bottomPairs_norms_grid : GlobalTheory.SqTop.GBig fun {D} _ _ {sc} G μ₀ C _ b => ∀ (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL), (∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)) → ArchimedeanHeightBound zA zA' (C * D.R.f * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ) * (Real.log b + Real.log ((maxWt D sc.cGap : ℝ) * (2 * (bigN D : ℝ)))) + C * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ))) + C * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl)) := by
  first | exact @GlobalTheory.ArchGrid.arch_grid | exact GlobalTheory.ArchGrid.arch_grid | (intros; apply GlobalTheory.ArchGrid.arch_grid <;> assumption)
