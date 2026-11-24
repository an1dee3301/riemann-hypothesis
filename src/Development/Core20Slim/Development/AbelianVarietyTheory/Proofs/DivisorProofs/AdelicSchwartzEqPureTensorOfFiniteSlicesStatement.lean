module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  first | exact @GlobalTheory.PureGlue.eq_pure_of_slices | exact GlobalTheory.PureGlue.eq_pure_of_slices | (intros; apply GlobalTheory.PureGlue.eq_pure_of_slices <;> assumption)
