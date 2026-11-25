module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransform
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensor
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

theorem pi_smul_nnreal {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  classical
  refine Measure.pi_eq (μ := fun i => c i • μ i) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib]
  norm_cast

theorem coordW_map_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam e he t ht
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  have hfm : ∀ a, Measurable (fun y : Ainf F ⊗[F] E => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * y) :=
    fun a => (continuous_const.mul continuous_id).measurable
  have hrow : ∀ a, (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) =
      (((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam := by
    intro a
    obtain ⟨u, hu⟩ := ht a
    have h := GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)
    rw [← hu] at h
    have hk := coordK_map_unit (Ainf F) σ hσ b lam u _ h
    rw [hu] at hk
    have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) _ (hfm a) _ hk
    simp only [Fintype.card_fin, ← pow_mul] at hk1
    exact hk1
  have hrm : ∀ a, Measurable (fun (x : Fin M → Ainf F ⊗[F] E) i =>
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) := fun a =>
    measurable_pi_iff.2 fun i => (hfm a).comp (measurable_pi_apply i)
  haveI : ∀ a, SigmaFinite ((Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i)) := fun a => by
    rw [hrow a]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (f := fun a (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) (fun a => (hrm a).aemeasurable)
  unfold GlobalTheory.CompanionTheory.SW.coordW
  refine hmap.trans ?_
  simp only [hrow]
  exact pi_smul_nnreal _ _

end GlobalTheory.CompanionTheory.SW.Dil
