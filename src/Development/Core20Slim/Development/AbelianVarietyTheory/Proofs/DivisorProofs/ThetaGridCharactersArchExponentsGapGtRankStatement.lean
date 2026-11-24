module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGridCharacters_archExponents_gap_gt_rank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, (((spW G i j).rank + (spW₁ G i j).rank : ℕ) : ℤ) < mα w - mβ w := by
  first | exact @GlobalTheory.SquareExps.exps | exact GlobalTheory.SquareExps.exps | (intros; apply GlobalTheory.SquareExps.exps <;> assumption)
