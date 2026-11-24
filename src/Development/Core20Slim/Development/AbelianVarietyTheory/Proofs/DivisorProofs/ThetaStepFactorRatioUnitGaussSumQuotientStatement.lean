module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotient
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  first | exact @GlobalTheory.SqStepArith.stepFac_ratio | exact GlobalTheory.SqStepArith.stepFac_ratio | (intros; apply GlobalTheory.SqStepArith.stepFac_ratio <;> assumption)
