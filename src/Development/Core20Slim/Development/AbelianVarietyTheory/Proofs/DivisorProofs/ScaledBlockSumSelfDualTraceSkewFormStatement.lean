module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledBlockSum_selfDual_traceSkewForm : ∀ {D : D7}, (∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) → ∀ (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e ↔
      ∀ x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) := by
  first | exact @GlobalTheory.SkewLat.pairLat_trace_selfDual | exact GlobalTheory.SkewLat.pairLat_trace_selfDual | (intros; apply GlobalTheory.SkewLat.pairLat_trace_selfDual <;> assumption)
