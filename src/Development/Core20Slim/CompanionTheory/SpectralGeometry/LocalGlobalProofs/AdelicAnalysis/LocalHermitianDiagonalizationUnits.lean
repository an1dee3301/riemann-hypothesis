module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraPropertiesStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormDiagonalizesStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormRepresentsUnitStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem hermR_unit_diagonalisable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (d : Fin n → Rˣ), IsUnit g.det ∧ (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * g := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ n S hS
  obtain ⟨hart, -, h2, hinv, hδ, hfix, hunit⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hσ R
  haveI : IsArtinianRing (R ⊗[F] E) := hart
  haveI : Finite (MaximalSpectrum (R ⊗[F] E)) := inferInstance
  have hrep := GlobalTheory.T.hermitian_unit_form_represents_unit (R ⊗[F] E) (sigR R σ) hinv h2 hδ
  obtain ⟨g, d, hg, hd, hgd⟩ :=
    GlobalTheory.T.hermitian_unit_form_diagonalizes (R ⊗[F] E) (sigR R σ) hinv hrep n (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S.2 hS
  choose r hr using fun i => hfix (d i) (hd i).2
  have hru : ∀ i, IsUnit (r i) := fun i => (hunit (r i)).1 (hr i ▸ (hd i).1)
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hdiag : Matrix.diagonal (fun i => (((hru i).unit : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) = Matrix.diagonal d := by
    congr 1
    funext i
    simp [hr i]
  refine ⟨g⁻¹, fun i => (hru i).unit, Matrix.isUnit_nonsing_inv_det g hg, ?_⟩
  rw [hdiag, ← hgd]
  have hc : cT (sigR R σ) g⁻¹ * cT (sigR R σ) g = 1 := by
    rw [← cT_mul, hgi, cT_one]
  calc (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))
      = (cT (sigR R σ) g⁻¹ * cT (sigR R σ) g) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g * g⁻¹) := by
        rw [hc, hgi, one_mul, mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SW
