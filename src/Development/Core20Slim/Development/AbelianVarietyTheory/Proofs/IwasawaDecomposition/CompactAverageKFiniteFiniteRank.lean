module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimensionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KAvgRank

open GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sigma_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (k₀ : KG ε) (w : H) :
    σ (toMK k₀) (kAvg ε σ e w) = kAvg ε σ (fun k => e (k₀⁻¹ * k)) w := by
  rw [kAvg, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ he w), kAvg,
    ← integral_mul_left_eq_self (fun k => e (k₀⁻¹ * k) • σ (toMK k) w) k₀]
  simp only [map_smul, inv_mul_cancel_left, sigma_K_mul hσ]

theorem exists_stable (hσ : IsURepOn (UJset ε) σ) {F : Submodule ℂ (KG ε → ℂ)} [FiniteDimensional ℂ F]
    (hc : ∀ φ ∈ F, Continuous φ) (hl : ∀ φ ∈ F, ∀ k₀ : KG ε, (fun k => φ (k₀ * k)) ∈ F) {e : KG ε → ℂ} (he : e ∈ F)
    (w : H) : ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      kAvg ε σ e w ∈ S ∧ IsKStableOn ε σ S := by
  let L : F →ₗ[ℂ] H :=
    { toFun := fun φ => kAvg ε σ φ w
      map_add' := fun x y => by
        simp only [kAvg, Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hσ (hc _ x.2) w) (integrable_avg hσ (hc _ y.2) w)
      map_smul' := fun c x => by
        simp only [kAvg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_assoc]
        exact integral_smul _ _ }
  refine ⟨LinearMap.range L, inferInstance, LinearMap.finrank_range_le L, ⟨⟨e, he⟩, rfl⟩, ?_⟩
  rintro k hk _ ⟨φ, rfl⟩
  obtain ⟨k₀, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
  exact ⟨⟨_, hl φ φ.2 k₀⁻¹⟩, (sigma_kAvg hσ (hc _ φ.2) k₀ w).symm⟩

theorem adjoint_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {Q : H →L[ℂ] H}
    (hQ : ∀ w, Q w = kAvg ε σ e w) {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H}
    (hz : z ∈ S) : ContinuousLinearMap.adjoint Q z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal']
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_left, hQ, inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪z, σ (toMK k) u⟫_ℂ = 0 := fun k => by
    have h := inner_K hσ k⁻¹ u z
    rw [inv_inv] at h
    rw [← h]
    exact Submodule.inner_right_of_mem_orthogonal (hK _ (toMK_mem_K _) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KAvgRank

namespace GlobalTheory.TypeSum

theorem kAvg_finite_rank : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), Orthonormal ℂ a ∧ (∀ j, IsKFin ε σ (a j)) ∧ (∀ j, IsKFin ε σ (c j)) ∧ ∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j := by
  intro n ε H _ _ _ σ h e ⟨F, hF, heF, hc, ht⟩
  have hσ := h.1
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ (hc e heF)
  let U : Submodule ℂ H := LinearMap.range (Q : H →ₗ[ℂ] H)
  have hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ Module.finrank ℂ F ∧
      u ∈ S ∧ IsKStableOn ε σ S := by
    rintro _ ⟨w, rfl⟩
    have := KAvgRank.exists_stable hσ hc (fun φ hφ k₀ => (ht φ hφ k₀).1) heF w
    rwa [← hQ] at this
  haveI : FiniteDimensional ℂ U := GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension n ε H σ h U _ hU
  let b := stdOrthonormalBasis ℂ U
  refine ⟨_, fun j => (b j : H), fun j => ContinuousLinearMap.adjoint Q (b j), ?_, fun j => ?_, fun j => ?_,
    fun w => ?_⟩
  · exact b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, h2, h3⟩
  · obtain ⟨S, h1, -, h2, h3⟩ := hU _ (b j).2
    exact ⟨S, h1, KAvgRank.adjoint_mem hσ (hc e heF) hQ h3 h2, h3⟩
  · have := congrArg Subtype.val (b.sum_repr' ⟨Q w, ⟨w, rfl⟩⟩)
    rw [← hQ]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    simpa using this.symm

end GlobalTheory.TypeSum
