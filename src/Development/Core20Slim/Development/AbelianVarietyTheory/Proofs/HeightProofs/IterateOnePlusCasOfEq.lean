module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def onePlusCas (σ : Mx n → (H →L[ℂ] H)) {d : ℕ} (X : Fin d → Mx n) (v : H) : H :=
  v - ∑ i, dRep σ (X i) (dRep σ (X i) v)

theorem sm_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) : Sm ε σ (onePlusCas σ X v) := by
  have h1 : ∀ i, Sm ε σ (dRep σ (X i) (dRep σ (X i) v)) := fun i =>
    dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv (hX i)) (hX i)
  exact (smooth (Jm ε) σ).sub_mem hv ((smooth (Jm ε) σ).sum_mem fun i _ => h1 i)

theorem sm_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) (r : ℕ) : Sm ε σ ((onePlusCas σ X)^[r] v) := by
  induction r with
  | zero => simpa using hv
  | succ r ih => rw [Function.iterate_succ_apply']; exact sm_onePlusCas hσ hX ih

theorem inner_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, onePlusCas σ X v⟫_ℂ = ⟪onePlusCas σ X b, v⟫_ℂ := by
  have key : ∀ i, ⟪b, dRep σ (X i) (dRep σ (X i) v)⟫_ℂ = ⟪dRep σ (X i) (dRep σ (X i) b), v⟫_ℂ := fun i => by
    have hv1 := dRep_mem (isUnit_Jm ε) hσ hv (hX i)
    have hb1 := dRep_mem (isUnit_Jm ε) hσ hb (hX i)
    rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 (hX i), inner_dRep (isUnit_Jm ε) hσ hb1 hv (hX i), neg_neg]
  simp only [onePlusCas, inner_sub_left, inner_sub_right, inner_sum, sum_inner, key]

theorem inner_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) (r : ℕ) :
    ⟪b, (onePlusCas σ X)^[r] v⟫_ℂ = ⟪(onePlusCas σ X)^[r] b, v⟫_ℂ := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih (sm_onePlusCas hσ hX hv), Function.iterate_succ_apply',
      inner_onePlusCas hσ hX (sm_iterate_onePlusCas hσ hX hb r) hv]

theorem onePlusCas_smul (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    (c : ℂ) {v : H} (hv : Sm ε σ v) : onePlusCas σ X (c • v) = c • onePlusCas σ X v := by
  have h : ∀ i, dRep σ (X i) (dRep σ (X i) (c • v)) = c • dRep σ (X i) (dRep σ (X i) v) := fun i =>
    Dw_smul hσ (l := [X i, X i]) (by simp [hX i]) c hv
  simp only [onePlusCas, h, smul_sub, Finset.smul_sum]

theorem iterate_onePlusCas_of_eq (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {v : H} (hv : Sm ε σ v) {μ : ℂ} (h : onePlusCas σ X v = μ • v) (r : ℕ) :
    (onePlusCas σ X)^[r] v = μ ^ r • v := by
  induction r with
  | zero => simp
  | succ r ih => rw [Function.iterate_succ_apply', ih, onePlusCas_smul hσ hX _ hv, h, smul_smul, pow_succ]

end GlobalTheory.TypeSum

end
