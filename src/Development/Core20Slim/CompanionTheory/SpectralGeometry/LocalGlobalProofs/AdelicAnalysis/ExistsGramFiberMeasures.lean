module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RestrFamily
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureDisintegrationFormulaStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Constructions
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
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramExist

theorem exists_gramFib : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν hμ hν
  have hR' := hR
  obtain ⟨htr, hlc, hsc, ht2, -, -, -, -⟩ := hR'
  obtain ⟨hKtr, hKlc, hKsc, hKt2, -, -, -, hKb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  have hKu := GlobalTheory.T.units_open_embedding_local_tensor F E σ hCM R hR
  obtain ⟨hXlc, hXsc, hXt2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM R n
  obtain ⟨g, hg, hgf⟩ := hlift M J hJ
  haveI := hKb n M
  have hinj : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage hc
  have hpre : ∀ B' : Set (HermR R σ n), gramR R σ J ⁻¹' (Subtype.val '' B') = g ⁻¹' B' := by
    intro B'
    ext X
    simp only [Set.mem_preimage, Set.mem_image, hgf X]
    exact hinj.mem_set_image
  have hglue := GlobalTheory.CompanionTheory.SW.FibreGlue.glue (Fin n → Fin M → R ⊗[F] E) (HermR R σ n)
    (Matrix (Fin n) (Fin n) (R ⊗[F] E)) μ ν (gramR R σ J) g Subtype.val hinj hg hgf
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} hBo ?_
  · obtain ⟨fib, hfib⟩ := hglue
    refine ⟨fib, ?_⟩
    have hU : {X | IsUnit (gramR R σ J X).det} =
        g ⁻¹' {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hgf X]
    unfold IsGramFib
    rw [hU]
    exact hfib
  · intro S hS
    obtain ⟨B, hB, hSB, hBu, fib, hfib⟩ :=
      GlobalTheory.T.gram_fiber_measure_disintegration_formula F E σ hCM M J hJ R hR n μ ν hμ hν S hS
    refine ⟨B, hB, hSB, fun S' hS' => hBu S' hS', fib, ?_⟩
    rw [← hpre]
    exact hfib

end GlobalTheory.CompanionTheory.SW.GramExist
