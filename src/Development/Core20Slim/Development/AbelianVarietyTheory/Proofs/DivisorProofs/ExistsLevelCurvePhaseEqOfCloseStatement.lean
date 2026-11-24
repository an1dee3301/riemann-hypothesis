module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCurvePhaseEqOfClose
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_curvePhase_eq_of_close : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
  ∀ {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E),
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  first | exact @GlobalTheory.PhaseMove.phase_eq | exact GlobalTheory.PhaseMove.phase_eq | (intros; apply GlobalTheory.PhaseMove.phase_eq <;> assumption)
