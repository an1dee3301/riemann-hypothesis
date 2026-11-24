module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphWittFlagCoordinates
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslNBPreserves
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslNC
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.HaarCoords

theorem haar_coords : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure ∧ lB.IsAddHaarMeasure ∧ lC.IsAddHaarMeasure ∧ SFinite μ ∧ SFinite lB ∧ SFinite lC ∧ Measurable (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∧ ∃ ν₀ : Measure (flagN d), ν₀.IsHaarMeasure ∧ ν₀.map Subtype.val = (μ.prod (lB.prod lC)).map (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d
  obtain ⟨iU1, iU2, iU3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨-, familyMassSecondLine, iM3, iM4, -⟩ := lattice_Mx D ρ S₀.rank
  obtain ⟨-, indexCSecond, iC3, iC4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨iN1, iN2, iN3, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have hcl : IsClosed ((skewA D ρ : Set (Mx D ρ ρ))) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : T2Space (skewA D ρ) := inferInstance
  let μ : Measure (UX D ρ) := Measure.haar
  let lB : Measure (Mx D ρ S₀.rank) := Measure.addHaar
  let lC : Measure (skewA D ρ) := Measure.addHaar
  obtain ⟨e, he⟩ := GlobalTheory.MixPer.flagCoord_homeo D S S₀ ρ d
  have hΦ : (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
      Subtype.val ∘ e := funext fun p => (he p).symm
  have hem : Measurable e := e.continuous.measurable
  refine ⟨μ, lB, lC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hΦ]; exact (continuous_subtype_val.comp e.continuous).measurable
  refine ⟨(μ.prod (lB.prod lC)).map e, ?_, ?_⟩
  · haveI := Measure.IsFiniteMeasureOnCompacts.map (μ.prod (lB.prod lC)) e
    haveI : ((μ.prod (lB.prod lC)).map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
    suffices h : ((μ.prod (lB.prod lC)).map e).IsMulLeftInvariant from ⟨⟩
    refine ⟨fun g => ?_⟩
    obtain ⟨p₀, hp₀⟩ := e.surjective g
    have hg : (g : GA D S) = d.levi p₀.1.1 * (d.nB p₀.2.1 * d.nC p₀.2.2) := by rw [← hp₀, he]
    obtain ⟨⟨u', hu'⟩, b', c'⟩ := p₀
    obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.HaarCoords.transl_nB_preserves D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance b'
    obtain ⟨Tc, hTc, hTc'⟩ := GlobalTheory.HaarCoords.transl_nC D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance c'
    let Ta : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) :=
      Prod.map (fun u => ⟨u', hu'⟩ * u) id
    have hTa : MeasurePreserving Ta (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) :=
      (measurePreserving_mul_left μ _).prod (MeasurePreserving.id _)
    have hT := hTa.comp (hTb.comp hTc)
    have key : (fun x => g * x) ∘ e = e ∘ (Ta ∘ Tb ∘ Tc) := by
      funext p
      apply Subtype.ext
      have h3 : ∀ q, d.levi (Ta q).1.1 * (d.nB (Ta q).2.1 * d.nC (Ta q).2.2) =
          d.levi u' * (d.levi q.1.1 * (d.nB q.2.1 * d.nC q.2.2)) := fun q => by
        simp only [Ta, Prod.map_fst, Prod.map_snd, id, Subgroup.coe_mul, map_mul, mul_assoc]
      simp only [Function.comp_apply, Subgroup.coe_mul, he]
      rw [h3, hTb', hTc', hg]
      simp only [mul_assoc]
    rw [Measure.map_map (measurable_const_mul g) hem, key, ← Measure.map_map hem hT.measurable, hT.map_eq]
  · rw [Measure.map_map continuous_subtype_val.measurable hem, hΦ]

end GlobalTheory.HaarCoords

end
