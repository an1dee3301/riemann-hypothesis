module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GLOpen

theorem continuousOn_ringInverse_of_isOpenEmbedding_units
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) :
    ContinuousOn (Ring.inverse : A → A) {x | IsUnit x} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← hA.continuousAt_iff]
  have h : (Ring.inverse ∘ Units.val : Aˣ → A) = fun v => ((v⁻¹ : Aˣ) : A) := by
    funext v
    exact Ring.inverse_unit v
  rw [h]
  exact Units.continuous_coe_inv.continuousAt

theorem isOpenEmbedding_val_GL
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) (n : ℕ) :
    IsOpenEmbedding (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) := by
  have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.det) :=
    continuous_id.matrix_det
  have hunit : ∀ M : Matrix (Fin n) (Fin n) A, IsUnit M ↔ IsUnit M.det :=
    fun M => Matrix.isUnit_iff_isUnit_det M
  have hadj : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.adjugate) :=
    continuous_id.matrix_adjugate
  have hopen : IsOpen {x : A | IsUnit x} := hA.isOpen_range
  refine ⟨Units.isEmbedding_val_mk' (f := fun M : Matrix (Fin n) (Fin n) A => M⁻¹) ?_
    fun u => (Matrix.coe_units_inv u).symm, ?_⟩
  · have hinv : ContinuousOn
        (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det • M.adjugate) {M | IsUnit M} := by
      have hri : ContinuousOn (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det)
          {M | IsUnit M} :=
        (GlobalTheory.CompanionTheory.SW.GLOpen.continuousOn_ringInverse_of_isOpenEmbedding_units A hA).comp hdet.continuousOn
          fun M hM => (hunit M).mp hM
      exact hri.smul hadj.continuousOn
    exact hinv.congr fun M _ => Matrix.inv_def M
  · have h : Set.range (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) =
        (fun M : Matrix (Fin n) (Fin n) A => M.det) ⁻¹' {x | IsUnit x} := by
      ext M
      exact hunit M
    rw [h]
    exact hopen.preimage hdet

end GlobalTheory.CompanionTheory.SW.GLOpen
