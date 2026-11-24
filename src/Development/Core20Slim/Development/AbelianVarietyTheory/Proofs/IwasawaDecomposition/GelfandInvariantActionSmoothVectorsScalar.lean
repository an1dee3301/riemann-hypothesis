module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionCommuteUnitaryRepSmoothStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurInnerEqPairClosableNormInvariantStatement
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.GelfScalar

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def LinAdjOn (D : Submodule ℂ H) (f : H → H) : Prop :=
  (∀ w ∈ D, f w ∈ D) ∧ (∀ v ∈ D, ∀ w ∈ D, f (v + w) = f v + f w) ∧ (∀ (c : ℂ), ∀ w ∈ D, f (c • w) = c • f w) ∧
    ∀ u ∈ D, ∃ u' ∈ D, ∀ w ∈ D, ⟪u, f w⟫_ℂ = ⟪u', w⟫_ℂ

variable {D : Submodule ℂ H}

theorem linAdjOn_id : LinAdjOn D fun w => w := ⟨fun _ hw => hw, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun u hu => ⟨u, hu, fun _ _ => rfl⟩⟩

theorem linAdjOn_zero : LinAdjOn D fun _ => 0 := by
  refine ⟨fun _ _ => D.zero_mem, fun _ _ _ _ => (add_zero 0).symm, fun c _ _ => (smul_zero c).symm,
    fun _ _ => ⟨0, D.zero_mem, fun w _ => ?_⟩⟩
  simp

theorem LinAdjOn.comp {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f (g w) := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => hf1 _ (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show f (g (v + w)) = f (g v) + f (g w)
    rw [hg2 v hv w hw, hf2 _ (hg1 v hv) _ (hg1 w hw)]
  · show f (g (c • w)) = c • f (g w)
    rw [hg3 c w hw, hf3 c _ (hg1 w hw)]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u₁ hu₁
    exact ⟨u₂, hu₂, fun w hw => (h₁ _ (hg1 w hw)).trans (h₂ w hw)⟩

theorem LinAdjOn.add {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f w + g w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => D.add_mem (hf1 w hw) (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_,
    fun u hu => ?_⟩
  · show f (v + w) + g (v + w) = (f v + g v) + (f w + g w)
    rw [hf2 v hv w hw, hg2 v hv w hw]
    abel
  · show f (c • w) + g (c • w) = c • (f w + g w)
    rw [hf3 c w hw, hg3 c w hw, smul_add]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u hu
    refine ⟨u₁ + u₂, D.add_mem hu₁ hu₂, fun w hw => ?_⟩
    show ⟪u, f w + g w⟫_ℂ = ⟪u₁ + u₂, w⟫_ℂ
    rw [inner_add_right, inner_add_left, h₁ w hw, h₂ w hw]

theorem LinAdjOn.smul {f : H → H} (hf : LinAdjOn D f) (a : ℂ) : LinAdjOn D fun w => a • f w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  refine ⟨fun w hw => D.smul_mem a (hf1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show a • f (v + w) = a • f v + a • f w
    rw [hf2 v hv w hw, smul_add]
  · show a • f (c • w) = c • a • f w
    rw [hf3 c w hw, smul_comm]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    refine ⟨(starRingEnd ℂ a) • u₁, D.smul_mem _ hu₁, fun w hw => ?_⟩
    show ⟪u, a • f w⟫_ℂ = ⟪(starRingEnd ℂ a) • u₁, w⟫_ℂ
    rw [inner_smul_right, inner_smul_left, h₁ w hw, Complex.conj_conj]

theorem linAdjOn_sum {ι : Type} (s : Finset ι) {f : ι → H → H} (hf : ∀ i, LinAdjOn D (f i)) :
    LinAdjOn D fun w => ∑ i ∈ s, f i w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact linAdjOn_zero
  · intro i s hi ih
    simp only [Finset.sum_insert hi]
    exact (hf i).add ih

theorem linAdjOn_foldr (l : List (H → H)) (hl : ∀ f ∈ l, LinAdjOn D f) :
    LinAdjOn D fun w => l.foldr (fun f acc => f acc) w := by
  induction l with
  | nil =>
    simp only [List.foldr_nil]
    exact linAdjOn_id
  | cons f l ih =>
    simp only [List.foldr_cons]
    exact (hl f (by simp)).comp (ih fun g hg => hl g (by simp [hg]))

theorem LinAdjOn.exists_extend {f : H → H} (hf : LinAdjOn D f) : ∃ A : H →ₗ[ℂ] H, ∀ w ∈ D, A w = f w := by
  obtain ⟨-, hf2, hf3, -⟩ := hf
  let g : D →ₗ[ℂ] H :=
    { toFun := fun x => f x
      map_add' := fun x y => hf2 x x.2 y y.2
      map_smul' := fun c x => hf3 c x x.2 }
  obtain ⟨A, hA⟩ := LinearMap.exists_extend g
  refine ⟨A, fun w hw => ?_⟩
  have key := LinearMap.congr_fun hA ⟨w, hw⟩
  exact key

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem linAdjOn_dRep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieG G) : LinAdjOn (smSub G π) (dRep π X) := by
  refine ⟨fun w hw => dRep_mem hG hπ hw hX, fun v hv w hw => dRep_add hv hw hX,
    fun c w hw => dRep_smul c hw hX, fun u hu => ⟨-dRep π X u, neg_mem (dRep_mem hG hπ hu hX), fun w hw => ?_⟩⟩
  rw [inner_dRep hG hπ hu hw hX, inner_neg_left]

theorem linAdjOn_dRepC (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (Z : Matrix (Fin n) (Fin n) ℂ) : LinAdjOn (smSub G π) (dRepC G π Z) := by
  obtain ⟨h₁, h₂⟩ := parts_mem hG hh Z
  exact (linAdjOn_dRep hG hπ h₁).add ((linAdjOn_dRep hG hπ h₂).smul Complex.I)

theorem linAdjOn_gelfH (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) :
    LinAdjOn (smSub G π) (gelfH G π k) := by
  show LinAdjOn (smSub G π) fun w => ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC G π (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
      (fun f acc => f acc) w
  refine linAdjOn_sum Finset.univ fun idx => linAdjOn_foldr _ fun g hg => ?_
  rw [List.mem_ofFn] at hg
  obtain ⟨a, rfl⟩ := hg
  exact linAdjOn_dRepC hG hh hπ _

end

theorem gelfH_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (k : ℕ), ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k w = c • w := by
  intro n ε H _ _ _ σ P G hP hPG hσ hirr k
  have hGu : IsUnit G := gram_unit hP hPG
  have hh : Gᴴ = G := gram_herm hPG
  have hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isURepOn_trRep hP hPG hσ
  have hirr' : IsIrredOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isIrredOn_trRep hP hPG hirr
  have hL := linAdjOn_gelfH hGu hh hπ k
  obtain ⟨A, hA⟩ := hL.exists_extend
  obtain ⟨-, -, -, hadj⟩ := hL
  have hnorm : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ v : H, ‖trRep σ P g v‖ = ‖v‖ := fun g hg v => hπ.2.1 g hg v
  have hAg : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      A (trRep σ P g w) = trRep σ P g (A w) := by
    intro g hg w hw
    rw [hA _ (rep_mem hGu hπ hw hg), hA w hw]
    exact GlobalTheory.T.gelfandInvariantAction_commute_unitaryRep_smooth n ε H σ P G hP hPG hσ k g hg w hw
  have h₁ : ∀ (i : Formalism.QuantumDeterminants.UH G) (v : H), ‖trRep σ P i.1 v‖ = ‖v‖ := fun i v => hnorm i.1 i.2 v
  have h₂ : ∀ i : Formalism.QuantumDeterminants.UH G, ∃ j : Formalism.QuantumDeterminants.UH G,
      (∀ v, trRep σ P j.1 (trRep σ P i.1 v) = v) ∧ ∀ v, trRep σ P i.1 (trRep σ P j.1 v) = v := by
    intro i
    have hu : IsUnit i.1.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_mem_UH hGu i.2)
    refine ⟨⟨i.1⁻¹, inv_mem_UH hGu i.2⟩, fun v => ?_, fun v => ?_⟩
    · rw [← rep_mul hπ (inv_mem_UH hGu i.2) i.2, Matrix.nonsing_inv_mul _ hu, rep_one hπ]
    · rw [← rep_mul hπ i.2 (inv_mem_UH hGu i.2), Matrix.mul_nonsing_inv _ hu, rep_one hπ]
  have h₃ : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ S, trRep σ P i.1 v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hinv => hirr' S hS fun g hg v hv => hinv ⟨g, hg⟩ v hv
  have h₄ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ smSub G (trRep σ P), trRep σ P i.1 v ∈ smSub G (trRep σ P) :=
    fun i v hv => rep_mem hGu hπ hv i.2
  have h₅ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P), ‖A (trRep σ P i.1 w)‖ = ‖A w‖ := by
    intro i w hw
    rw [hAg i.1 i.2 w hw, hnorm i.1 i.2]
  have h₆ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ‖(LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)‖ = ‖(LinearMap.id : H →ₗ[ℂ] H) w‖ := by
    intro i w _
    simp only [LinearMap.id_apply]
    exact hnorm i.1 i.2 w
  have h₇ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ⟪A (trRep σ P i.1 w), (LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)⟫_ℂ =
        ⟪A w, (LinearMap.id : H →ₗ[ℂ] H) w⟫_ℂ := by
    intro i w hw
    simp only [LinearMap.id_apply]
    rw [hAg i.1 i.2 w hw, rep_inner hπ i.2]
  have h₈ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f hu hu0 hAu
    apply eq_zero_of_inner_smooth hP hPG hσ
    intro v hv
    obtain ⟨v', -, hvv⟩ := hadj v hv
    have t₁ : Tendsto (fun i => ⟪v, A (u i)⟫_ℂ) atTop (𝓝 ⟪v, f⟫_ℂ) := tendsto_const_nhds.inner hAu
    have t₂ : Tendsto (fun i => ⟪v', u i⟫_ℂ) atTop (𝓝 ⟪v', (0 : H)⟫_ℂ) :=
      tendsto_const_nhds.inner hu0
    rw [inner_zero_right] at t₂
    refine tendsto_nhds_unique t₁ (t₂.congr fun i => ?_)
    rw [hA _ (hu i), hvv _ (hu i)]
  have h₉ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => (LinearMap.id : H →ₗ[ℂ] H) (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f _ hu0 hu
    simp only [LinearMap.id_apply] at hu
    exact tendsto_nhds_unique hu hu0
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant (Formalism.QuantumDeterminants.UH G) H H (fun i => trRep σ P i.1) (smSub G (trRep σ P))
    h₁ h₂ h₃ h₄ A LinearMap.id h₅ h₆ h₇ h₈ h₉
  refine ⟨starRingEnd ℂ c, fun w hw => ?_⟩
  rw [← hA w hw]
  apply ext_inner_smooth hP hPG hσ
  intro u hu
  have e₁ : ⟪A w, u⟫_ℂ = ⟪starRingEnd ℂ c • w, u⟫_ℂ := by
    have e := hc w hw u hu
    rw [LinearMap.id_apply] at e
    rw [e, inner_smul_left, Complex.conj_conj]
  rw [← inner_conj_symm, e₁, inner_conj_symm]

end GlobalTheory.SmVec.GelfScalar
