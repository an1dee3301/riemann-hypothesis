module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumStepCharacterTwistPlaceDvd
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussSum_stepCharacter_twistPlace_dvd : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : AddChar (AF D.host.F) ℂ), PsiUnr ψ v →
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 →
      ∃ g : 𝓞 D.what₂.LL, D.what₂.embLL (g : D.what₂.LL) = gauss ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) ∧
        g ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.what₂.LL) := by
  first | exact @GlobalTheory.TwistGaussInt.gauss_dvd | exact GlobalTheory.TwistGaussInt.gauss_dvd | (intros; apply GlobalTheory.TwistGaussInt.gauss_dvd <;> assumption)
