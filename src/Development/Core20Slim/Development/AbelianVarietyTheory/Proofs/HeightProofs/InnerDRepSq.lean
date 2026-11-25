module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def casOp (σ : Mx n → (H →L[ℂ] H)) {d e : ℕ} (X : Fin d → Mx n) (Y : Fin e → Mx n) (v : H) : H :=
  ∑ b, dRep σ (Y b) (dRep σ (Y b) v) - ∑ i, dRep σ (X i) (dRep σ (X i) v)

theorem sm_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {v : H} (hv : Sm ε σ v) :
    Sm ε σ (dRep σ Z (dRep σ Z v)) :=
  dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv hZ) hZ

theorem inner_dRep_sq (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {b v : H} (hb : Sm ε σ b)
    (hv : Sm ε σ v) : ⟪b, dRep σ Z (dRep σ Z v)⟫_ℂ = ⟪dRep σ Z (dRep σ Z b), v⟫_ℂ := by
  have hv1 := dRep_mem (isUnit_Jm ε) hσ hv hZ
  have hb1 := dRep_mem (isUnit_Jm ε) hσ hb hZ
  rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 hZ, inner_dRep (isUnit_Jm ε) hσ hb1 hv hZ, neg_neg]

variable {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}

theorem sm_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) : Sm ε σ (casOp σ X Y v) :=
  (smooth (Jm ε) σ).sub_mem ((smooth (Jm ε) σ).sum_mem fun b _ => sm_dRep_sq hσ (hY b) hv)
    ((smooth (Jm ε) σ).sum_mem fun i _ => sm_dRep_sq hσ (hX i) hv)

theorem inner_casOp (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {b v : H}
    (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, casOp σ X Y v⟫_ℂ = ⟪casOp σ X Y b, v⟫_ℂ := by
  simp only [casOp, inner_sub_left, inner_sub_right, inner_sum, sum_inner, inner_dRep_sq hσ (hX _) hb hv,
    inner_dRep_sq hσ (hY _) hb hv]

theorem casOp_add (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {x y : H}
    (hx : Sm ε σ x) (hy : Sm ε σ y) : casOp σ X Y (x + y) = casOp σ X Y x + casOp σ X Y y := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (x + y)) = dRep σ Z (dRep σ Z x) + dRep σ Z (dRep σ Z y) :=
    fun Z hZ => Dw_add hσ (l := [Z, Z]) (by simp [hZ]) hx hy
  simp only [casOp, h _ (hX _), h _ (hY _), Finset.sum_add_distrib]
  abel

theorem casOp_smul (hσ : IsURepOn (UJset ε) σ) (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) (c : ℂ)
    {x : H} (hx : Sm ε σ x) : casOp σ X Y (c • x) = c • casOp σ X Y x := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (c • x)) = c • dRep σ Z (dRep σ Z x) :=
    fun Z hZ => Dw_smul hσ (l := [Z, Z]) (by simp [hZ]) c hx
  simp only [casOp, h _ (hX _), h _ (hY _), ← Finset.smul_sum, smul_sub]

end GlobalTheory.TypeSum.CasBasis

end
