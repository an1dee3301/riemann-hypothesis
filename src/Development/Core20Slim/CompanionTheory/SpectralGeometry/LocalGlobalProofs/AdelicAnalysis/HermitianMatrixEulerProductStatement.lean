module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProduct
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrix_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) (g.map (inclR (Ainf F))) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g.map (inclR (Ainf F))) → ν.map τ = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ ν : Measure (HermR (Fv F v) σ n), ν.IsAddHaarMeasure → ∀ τ : HermR (Fv F v) σ n → HermR (Fv F v) σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) (g.map (inclR (Fv F v))) * (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * g.map (inclR (Fv F v))) → ν.map τ = c v • ν) := by
  first | exact @GlobalTheory.CompanionTheory.SW.pf_herm | exact GlobalTheory.CompanionTheory.SW.pf_herm | (intros; apply GlobalTheory.CompanionTheory.SW.pf_herm <;> assumption)
