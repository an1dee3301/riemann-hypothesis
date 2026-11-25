module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebraStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirDifferenceOperatorEquivariantStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis

theorem casimir_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hX, hY⟩ := GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra n ε
  have hG := GlobalTheory.T.casimirDifferenceOperator_equivariant n ε H σ h
  obtain ⟨u, χ, hu, hu0, hχ⟩ := GlobalTheory.T.exists_smooth_eigenvector_casimirDifferenceOperator n ε H σ _ _ (kB ε) (pB ε) h hX hY fun k hk v hv => hG k (K_le_UJ hk) v hv
  have hχr : (starRingEnd ℂ) χ = χ := by
    have e := inner_casOp h.1 hX hY hu hu
    rw [hχ, inner_smul_left, inner_smul_right] at e
    have hne : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hu0
    exact (mul_right_cancel₀ hne e).symm
  refine ⟨χ, fun v hv => ?_⟩
  have hws : Sm ε σ (casOp σ (kB ε) (pB ε) v - χ • v) :=
    (smooth (Jm ε) σ).sub_mem (sm_casOp h.1 hX hY hv) ((smooth (Jm ε) σ).smul_mem χ hv)
  have h0 : ∀ g ∈ UJset ε,
      ((innerSL ℂ (casOp σ (kB ε) (pB ε) v - χ • v) : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) (σ g u) = 0 := by
    intro g hg
    have hgu := hu.translate h.1 hg
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sub_left, inner_smul_left, hχr]
    rw [← inner_casOp h.1 hX hY hv hgu, hG g hg u hu, hχ, map_smul, inner_smul_right, sub_self]
  have hz := h.eq_zero_of_orbit (sobCont_inner _) hu hu0 h0 hws
  simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hz
  simp only [casOp, sub_sub, sub_eq_zero] at hz
  rw [hz, add_comm]

end GlobalTheory.TypeSum.CasBasis

end
