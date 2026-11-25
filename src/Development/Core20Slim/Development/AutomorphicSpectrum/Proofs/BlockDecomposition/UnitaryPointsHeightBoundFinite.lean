module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
public import Development.Core20Slim.CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AnisotropicUnitaryRes
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianOrthogonal
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionHeight
public import Development.Core20Slim.GroundTheory.AutomorphicForms.UnitaryGroupScheme
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Mahler

open GlobalTheory.CompanionTheory.RedCov.Bridge

def pointsHomeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GAd (conj F E).toAlgHom J ≃ₜ unitaryPoints F E J 𝔸[F] where
  toFun g := ⟨matHom _ _ J g, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).1 g.2⟩
  invFun u := ⟨u.1, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).2 u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

theorem exists_isCompact_of_le_hgt : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  intro hM F E _ _ _ _ _ σ hσ n J hJ t ht
  obtain ⟨hF, hE', h2, hc⟩ := hσ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  let e := pointsHomeo (F := F) (E := E) J
  obtain ⟨Ω, hΩ, hcov⟩ := hM F E n J hu
    (e '' {g | ∀ v : Fin n → E, v ≠ 0 → t ≤ hgt _ J g v}) t ht (by
      rintro _ ⟨g, hg, rfl⟩ x hx
      obtain ⟨v, rfl⟩ := cvec_surjective (F := F) (E := E) (n := n) x
      have hv : v ≠ 0 := by
        rintro rfl
        apply hx
        funext p
        simp [cvec]
      have := hg v hv
      rw [hgt_eq] at this
      exact this)
  refine ⟨e ⁻¹' Ω, e.isCompact_preimage.2 hΩ, fun g hg => ?_⟩
  obtain ⟨θ, hθ, hθΩ⟩ := hcov (e g) ⟨g, hg, rfl⟩
  rw [← CompanionTheory.SWFin.HFin_eq, Subgroup.mem_subgroupOf] at hθ
  refine ⟨e.symm θ, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 hθ
  · exact hθΩ

end GlobalTheory.CompanionTheory.RedCov.Mahler
