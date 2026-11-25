module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagFormGlue

open GlobalTheory.DiagForm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  change (eI F κ).symm (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i))) = p.1
  simp only [RingEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem glue_shiftOf (x : κ → AdeleRing (𝓞 F) F) : glue (shiftOf x) = x := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ ((eI F κ).symm _) i) = (x i).1
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact RingEquiv.symm_apply_apply _ _

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  conv_lhs => rw [← shiftOf_glue q]
  exact glue_add_shiftOf p (glue q)

theorem ringEquiv_symm_eq :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace F).symm := by
  funext z
  apply (GroundTheory.Global.homeomorphMixedSpace F).injective
  rw [Homeomorph.apply_symm_apply, GroundTheory.Global.homeomorphMixedSpace_apply, RingEquiv.apply_symm_apply]

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) := by
  refine continuous_pi fun i => ?_
  show Continuous fun p : Vi F κ × Vf F κ =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i), p.2 i) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [ringEquiv_symm_eq]
  exact ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp
    ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AdeleRing (𝓞 F) F) → Vi F κ × Vf F κ) := by
  refine Continuous.prodMk ((eI F κ).symm.continuous.comp (continuous_pi fun i => ?_))
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  show Continuous fun x : κ → AdeleRing (𝓞 F) F => GroundTheory.Global.homeomorphMixedSpace F (x i).1
  exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))


variable (F κ) in
def glueEquiv : (Vi F κ × Vf F κ) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := glue_add

theorem exists_glue_measure :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    ∃ c : NNReal, 0 < c ∧ (mu F κ).map glue = c • (adeleMeasurePi F (ι := κ)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance
  haveI : ((mu F κ).map (glueEquiv F κ)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map _ (glueEquiv F κ) continuous_glue continuous_shiftOf
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueEquiv F κ)) (adeleMeasurePi F (ι := κ))
  refine ⟨_, ?_, h⟩
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_smul] at h
  exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := (mu F κ).map (glueEquiv F κ))).open_pos
    Set.univ isOpen_univ Set.univ_nonempty (by rw [h]; rfl)


variable (F κ) in
def glueMEquiv :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    (Vi F κ × Vf F κ) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  (Homeomorph.mk (glueEquiv F κ).toEquiv continuous_glue continuous_shiftOf).toMeasurableEquiv

end GlobalTheory.DiagFormGlue

namespace GlobalTheory

theorem diagForm_glue_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ H : (κ → AF F) → ℂ, (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔
      Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := by
  intro F _ _ κ _
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  obtain ⟨c, hc, hmap⟩ := DiagFormGlue.exists_glue_measure (F := F) (κ := κ)
  have hmap' : (GlobalTheory.DiagForm.mu F κ).map (DiagFormGlue.glueMEquiv F κ) = c • adeleMeasurePi F (ι := κ) := hmap
  refine ⟨c, hc, fun H => ⟨?_, ?_⟩⟩
  · rw [← (integrable_smul_measure (f := H) (μ := adeleMeasurePi F (ι := κ)) (c := (c : ENNReal))
      (by exact_mod_cast hc.ne') ENNReal.coe_ne_top)]
    have e2 : (c : ENNReal) • adeleMeasurePi F (ι := κ) = c • adeleMeasurePi F (ι := κ) := rfl
    rw [e2, ← hmap', integrable_map_equiv]
    rfl
  · have h1 := integral_map_equiv (μ := GlobalTheory.DiagForm.mu F κ) (DiagFormGlue.glueMEquiv F κ) H
    rw [hmap', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h1
    exact h1.symm
end GlobalTheory
