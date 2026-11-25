module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousScale
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

theorem scaleInf : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  intro F E _ _ _ _ _ σ hσ n M μ ν hμ hν
  classical
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨A, hA, hAf⟩ := exists_scale_tuples σ hσ (Ainf F) hR n M μ hμ
  obtain ⟨B, hB, hBf⟩ := exists_scale_herm σ hσ (Ainf F) hR n ν hν
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jB
  haveI := jT2
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  refine ⟨A, B, hA, hB, fun g hg => ?_⟩
  have hTc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    exact continuous_finsetSum _ fun c _ => ((continuous_apply_apply c i).mul continuous_const)
  have hTm : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := hTc.measurable
  let τ₀ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S =>
    ⟨conjT (Ainf F) σ g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, conj_mem (Ainf F) hs _ S⟩
  have hτ₀c : Continuous τ₀ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hcT : ∀ S : HermR (Ainf F) σ n, ((τ₀ S : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
      cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g := fun S => rfl
  have hB0 := hBf g hg τ₀ (fun S => rfl)
  refine ⟨?_, ?_, hAf g hg, fun τ hτ => ?_⟩
  · intro h0
    have h1 := hAf g hg
    rw [h0, zero_smul, Measure.map_eq_zero_iff hTm.aemeasurable] at h1
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [h1]; simp)
  · intro h0
    rw [h0, zero_smul, Measure.map_eq_zero_iff hτ₀c.measurable.aemeasurable] at hB0
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [hB0]; simp)
  · have : τ = τ₀ := funext fun S => Subtype.ext ((hτ S).trans (hcT S).symm)
    rw [this]
    exact hB0

end GlobalTheory.CompanionTheory.SW.HaarScale
