module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Cast
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Quotient
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
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_factor_of_bound {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Φ : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖ℓ w‖ ≤ C * ‖Φ w‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ w, Λ (Φ w) = ℓ w := by
  have hk : LinearMap.ker Φ ≤ LinearMap.ker ℓ := fun w hw => by
    have := h w
    rw [LinearMap.mem_ker.1 hw, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let f₀ : LinearMap.range Φ →ₗ[ℂ] ℂ := (LinearMap.ker Φ).liftQ ℓ hk ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ w, f₀ ⟨Φ w, LinearMap.mem_range_self Φ w⟩ = ℓ w := fun w => by
    simp only [f₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ x, ‖f₀ x‖ ≤ C * ‖x‖ := by
    rintro ⟨_, w, rfl⟩
    exact (congrArg norm (hf w)).le.trans (h w)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (f₀.mkContinuous C hb)
  exact ⟨g, fun w => (hg ⟨Φ w, LinearMap.mem_range_self Φ w⟩).trans (hf w)⟩

theorem exists_inner_of_pi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}
    (Λ : (Fin m → H) →L[ℂ] ℂ) : ∃ a : Fin m → H, ∀ x, Λ x = ∑ i, ⟪a i, x i⟫_ℂ := by
  refine ⟨fun i => (InnerProductSpace.toDual ℂ H).symm (Λ.comp (ContinuousLinearMap.single ℂ (fun _ => H) i)),
    fun x => ?_⟩
  simp only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Finset.univ_sum_single]

theorem sobCont_repr : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∃ (m : ℕ) (ls : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (a : Fin m → H), (∀ i, ∀ X ∈ ls i, X ∈ lieG G) ∧ ∀ w ∈ smSub G (trRep σ P), ℓ w = ∑ i, ⟪a i, word (trRep σ P) (ls i) w⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ ⟨S, C, hS, hC⟩
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hl : ∀ i : Fin S.length, ∀ X ∈ S.get i, X ∈ lieG G := fun i => hS _ (List.get_mem S i)
  let Φ : smSub G (trRep σ P) →ₗ[ℂ] (Fin S.length → H) :=
    { toFun := fun w i => word (trRep σ P) (S.get i) w
      map_add' := fun v w => funext fun i => word_add hG hπ (hl i) v.2 w.2
      map_smul' := fun c w => funext fun i => word_smul hG hπ (hl i) c w.2 }
  have hb : ∀ w, ‖(ℓ ∘ₗ (smSub G (trRep σ P)).subtype) w‖ ≤ (|C| * S.length) * ‖Φ w‖ := fun w => by
    refine (hC w w.2).trans ?_
    have h1 : (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum ≤ S.length * ‖Φ w‖ := by
      have := List.sum_le_card_nsmul (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖) ‖Φ w‖ (by
        intro x hx
        obtain ⟨l, hl', rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hl'
        exact norm_le_pi_norm (Φ w) i)
      simpa using this
    have h0 : 0 ≤ (S.map fun l => ‖List.foldr (dRep (trRep σ P)) (w : H) l‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    rw [mul_assoc]
    exact mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
  obtain ⟨Λ, hΛ⟩ := exists_factor_of_bound Φ _ _ hb
  obtain ⟨a, ha⟩ := exists_inner_of_pi Λ
  exact ⟨S.length, S.get, a, hl, fun w hw => (hΛ ⟨w, hw⟩).symm.trans (ha _)⟩

end GlobalTheory.SmVec
