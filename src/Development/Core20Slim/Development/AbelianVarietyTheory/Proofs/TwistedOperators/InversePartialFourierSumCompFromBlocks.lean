module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftResMulSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Function
public import Init.Data.Nat.Div.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section
namespace GlobalTheory.BlockSubstFourier

theorem invFourierSum_comp_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) (hΦ : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ)
    (M₁ : GL D₁ k) (hM₁ : M₁ ∈ KO k D₁) (M₂ : GL D₂ k) (hM₂ : M₂ ∈ KO k D₂) (X : Matrix A (D₁ ⊕ D₂) k) :
    invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [compl_block_one] at hΦ ⊢
  set P := Assignment.two.block D₁ D₂ with hP
  have inr_mem : ∀ j : D₂, (Sum.inr j : D₁ ⊕ D₂) ∈ P := fun j => by simp [hP, Assignment.block]
  have inl_nmem : ∀ j : D₁, (Sum.inl j : D₁ ⊕ D₂) ∉ P := fun j => by simp [hP, Assignment.block]
  let eP : D₂ ≃ P := Equiv.ofBijective (fun j => ⟨Sum.inr j, inr_mem j⟩) ⟨fun a b h => by simpa using h, by
    rintro ⟨(j | j), h⟩
    · exact absurd h (inl_nmem j)
    · exact ⟨j, rfl⟩⟩
  have eP_apply : ∀ j, (eP j : D₁ ⊕ D₂) = Sum.inr j := fun j => rfl
  set M := fromBlocks M₁.val 0 0 M₂.val with hM
  set M' := fromBlocks M₁.val 0 0 (invT M₂).val with hM'
  set Nk : Matrix P P k := (invT M₂).val.submatrix eP.symm eP.symm with hNk
  have hNk_apply : ∀ a b, Nk (eP a) (eP b) = (invT M₂).val a b := fun a b => by simp [hNk]
  obtain ⟨u, hu⟩ := invT_mem_KO hM₂
  let N : Matrix P P 𝒪[k] := u.val.submatrix eP.symm eP.symm
  let N' : Matrix P P 𝒪[k] := (u⁻¹).val.submatrix eP.symm eP.symm
  have hNN : N * N' = 1 := by
    simp only [N, N', Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hNmap : N.map (fun x => (x : k)) = Nk := by
    rw [hNk, ← hu]; ext i j; rfl
  have hM₂i := (mem_KO_iff M₂).1 hM₂

  set X₂ : Matrix A D₂ k := X.submatrix id Sum.inr with hX₂
  have hXM₂ : (X * M).submatrix id Sum.inr = X₂ * M₂.val := by
    ext i j; simp [hM, hX₂, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
  have condP : ∀ Z : Matrix A (D₁ ⊕ D₂) k,
      (∀ i, ∀ j ∈ P, Z i j ∈ 𝒪[k]) ↔ ∀ i (j : D₂), Z i (Sum.inr j) ∈ 𝒪[k] := by
    intro Z
    refine forall_congr' fun i => ⟨fun h j => h _ (inr_mem j), fun h j hj => ?_⟩
    rcases j with j | j
    · exact absurd hj (inl_nmem j)
    · exact h j
  have hsum : ∀ (T : Matrix A P k) (Y : Matrix A (D₁ ⊕ D₂) k),
      pairCols P Y T = trace (T.submatrix id eP * (Y.submatrix id Sum.inr)ᵀ) := by
    intro T Y
    simp only [pairCols, trace, Matrix.mul_apply, diag_apply, transpose_apply, submatrix_apply, id]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Equiv.sum_comp eP (fun j => T i j * Y i j)).symm
  have hTN : ∀ T : Matrix A P k, (T * Nk).submatrix id eP = T.submatrix id eP * (invT M₂).val := by
    intro T; ext i j
    simp only [submatrix_apply, id, Matrix.mul_apply]
    rw [← Equiv.sum_comp eP]
    simp [hNk_apply]
  have hset : ∀ T : Matrix A P k, setCols P X T * M' = setCols P (X * M) (T * Nk) := by
    intro T; ext i (j | j)
    · simp [hM, hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
    · have h1 : setCols P (X * M) (T * Nk) i (Sum.inr j) = (T.submatrix id eP * (invT M₂).val) i j := by
        rw [← hTN]; simp only [setCols, Matrix.of_apply, dif_pos (inr_mem j), submatrix_apply, id]; rfl
      rw [h1]
      simp [hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
      rfl
  have hpair : ∀ T : Matrix A P k, pairCols P (X * M) (T * Nk) = pairCols P X T := by
    intro T
    rw [hsum, hsum, hTN, hXM₂, transpose_mul, invT_val]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ M₂.valᵀ, ← transpose_mul, Units.mul_inv, transpose_one,
      Matrix.one_mul]
  have setCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      setCols P Y (T + T') = setCols P Y T + setCols P 0 T' := by
    intro Y T T'; ext i j
    by_cases h : j ∈ P <;> simp [setCols, h]
  have pairCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      pairCols P Y (T + T') = pairCols P Y T + pairCols P Y T' := by
    intro Y T T'; simp [pairCols, add_mul, Finset.sum_add_distrib]
  have hcZ : ∀ z : k, valuation k z ≤ valuation k ((ϖ ^ e : kˣ) : k) → (((ϖ ^ e)⁻¹ : kˣ) : k) * z ∈ 𝒪[k] := by
    intro z hz
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
    exact hz
  rw [invFourierSum_apply, invFourierSum_apply]
  by_cases hX : ∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]
  · have hXM : ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      rw [condP] at hX ⊢
      intro i j
      have := congrFun (congrFun hXM₂ i) j
      simp only [submatrix_apply, id] at this
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (hX i l) (hM₂i.1 l j)
    rw [if_pos hX, if_pos hXM]
    let F : Matrix A P k → ℂ := fun T =>
      Φ (setCols P (X * M) ((ϖ ^ e)⁻¹ • T)) * (ψ (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • T)) : ℂ)
    have step : ∀ S : A → P → Res k e,
        Φ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S) * M') * (ψ (-pairCols P X ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) =
          F (liftRes S * N.map (fun x => (x : k))) := by
      intro S
      rw [hNmap]
      simp only [F]
      rw [← Matrix.smul_mul, ← hset, hpair]
    have hF : ∀ T Z : Matrix A P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        F (T + Z) = F T := by
      intro T Z hZ
      simp only [F, smul_add, setCols_add', pairCols_add', neg_add, AddChar.map_add_eq_mul]
      have hcZ' : ∀ i j, ((ϖ ^ e)⁻¹ • Z) i j ∈ 𝒪[k] := fun i j => by
        simpa [Units.smul_def] using hcZ _ (hZ i j)
      rw [hΦ.2, triv (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • Z)), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        exact mul_mem (hcZ' i j) (hXM i j j.2)
      · refine FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simpa [setCols, hj] using hcZ' i ⟨j, hj⟩
        · simp [setCols, hj]
    simp only [step]
    exact GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hNN F hF
  · have hXM : ¬ ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      intro h'
      apply hX
      rw [condP] at h' ⊢
      intro i j
      have hX₂ : X₂ = (X * M).submatrix id Sum.inr * (M₂⁻¹).val := by
        rw [hXM₂, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      have : X i (Sum.inr j) = ((X * M).submatrix id Sum.inr * (M₂⁻¹).val) i j := congrFun (congrFun hX₂ i) j
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (h' i l) (hM₂i.2 l j)
    rw [if_neg hX, if_neg hXM]

end GlobalTheory.BlockSubstFourier
