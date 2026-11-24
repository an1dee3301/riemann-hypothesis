module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vector_isThetaFunction_definite_pair : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ T, IsThetaFunO X.ψ X.A X.B (X.fock T) := by
  first | exact @GlobalTheory.NormDict.fock_isThetaFunO | exact GlobalTheory.NormDict.fock_isThetaFunO | (intros; apply GlobalTheory.NormDict.fock_isThetaFunO <;> assumption)
