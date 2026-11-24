module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelLeviDeterminantIntegralSelfDualLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.Core.Rk.AInt.aH_mem_intLoc | exact GlobalTheory.Core.Rk.AInt.aH_mem_intLoc | (intros; apply GlobalTheory.Core.Rk.AInt.aH_mem_intLoc <;> assumption)
