module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMemStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdealStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondESupConj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualSkewIdealLattice_isSelfDual : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ), 𝔪 ≠ ⊥ → SD D (GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N) := by
  first | exact @GlobalTheory.SkewLatSD.skewLat_sd | exact GlobalTheory.SkewLatSD.skewLat_sd | (intros; apply GlobalTheory.SkewLatSD.skewLat_sd <;> assumption)
