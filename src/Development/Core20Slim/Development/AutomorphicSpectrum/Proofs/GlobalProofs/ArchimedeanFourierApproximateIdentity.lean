module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass

theorem boxMass : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ lf : Measure (Af F), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v, MeasurableSet (A v)) → MeasurableSet (Coef.boxA S A) ∧ lf (Coef.boxA S A) = ∏ v ∈ S, lam v (A v) := by
  intro F _ _ lam hlam lf hlf h1 S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Unit → Fv F v) := fun v => {x | x () ∈ A v}
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => measurable_pi_apply () (hA v)
  let T : Set (Unit → Af F) := {x | (∀ v ∈ S, (fun i => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (x i)) ∈ A' v) ∧
    ∀ v, v ∉ S → ∀ i, HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (x i) ∈ v.adicCompletionIntegers F}
  have hT : T = (GlobalTheory.CompanionTheory.SW.AfBox.offS (F := F) Unit S : Set (Unit → Af F)) ∩
      GlobalTheory.CompanionTheory.SW.AfBox.compS Unit S ⁻¹' (Set.pi Set.univ fun v : S => A' v.1) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, fun v _ => hx1 v.1 v.2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun v hv => hx2 ⟨v, hv⟩ (Set.mem_univ _), hx1⟩
  have hTm : MeasurableSet T := by
    rw [hT]
    exact (GlobalTheory.CompanionTheory.SW.AfBox.isOpen_offS Unit S).measurableSet.inter
      ((GlobalTheory.CompanionTheory.SW.AfBox.continuous_compS Unit S).measurable (MeasurableSet.univ_pi fun v => hA' v.1))
  have hbox : Coef.boxA S A = (MeasurableEquiv.funUnique Unit (Af F)).symm ⁻¹' T := by
    ext y
    simp only [Coef.boxA, T, A', Set.mem_preimage, Set.mem_setOf_eq, MeasurableEquiv.funUnique_symm_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv _ => h2 v hv⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv => h2 v hv ()⟩
  have hmeas : MeasurableSet (Coef.boxA S A) := by
    rw [hbox]
    exact (MeasurableEquiv.funUnique Unit (Af F)).symm.measurable hTm
  refine ⟨hmeas, ?_⟩
  have hpb := GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 Unit S A' hA'
  have hmp := measurePreserving_funUnique lf Unit
  have hT' : T = (MeasurableEquiv.funUnique Unit (Af F)) ⁻¹' Coef.boxA S A := by
    rw [hbox, ← Set.preimage_comp]
    ext x
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [show (MeasurableEquiv.funUnique Unit (Af F)).symm ((MeasurableEquiv.funUnique Unit (Af F)) x) = x
      from (MeasurableEquiv.funUnique Unit (Af F)).symm_apply_apply x]
  change (Measure.pi fun _ : Unit => lf) T = _ at hpb
  rw [hT', hmp.measure_preimage hmeas.nullMeasurableSet] at hpb
  rw [hpb]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : A' v = (MeasurableEquiv.funUnique Unit (Fv F v)) ⁻¹' A v := by
    ext x
    rfl
  rw [hv, (measurePreserving_funUnique (lam v) Unit).measure_preimage (hA v).nullMeasurableSet]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass
