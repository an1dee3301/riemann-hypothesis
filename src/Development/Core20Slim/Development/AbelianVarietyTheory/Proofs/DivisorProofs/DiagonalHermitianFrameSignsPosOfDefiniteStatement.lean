module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHermitianFrameSignsPosOfDefinite
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite : ∀ (D : D7) (V : HSp D) (F : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau),
    Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 → ∀ j, F.ε τ j = true := by
  first | exact @GlobalTheory.DefiniteFrame.frame_signs_pos | exact GlobalTheory.DefiniteFrame.frame_signs_pos | (intros; apply GlobalTheory.DefiniteFrame.frame_signs_pos <;> assumption)
