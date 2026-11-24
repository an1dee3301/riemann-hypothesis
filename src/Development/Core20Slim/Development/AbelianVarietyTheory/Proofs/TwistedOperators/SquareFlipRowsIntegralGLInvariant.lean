module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPrimFrameGlMulIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameTestFunctionTransposeIntegralGLMulEqCharStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumQuotientIntegerMatricesInvariantIntegralGLMulStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
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
public import Mathlib.Algebra.BigOperators.Ring.Finset
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
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
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.SquareFlipRows

theorem squareFlip_one_rows : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ u ∈ KO k A, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      (ν (gdet u) : ℂ) * squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ
          (fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂)) =
        squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ X := by

  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ u hu X
  have hM : (invT u⁻¹).val = u.valᵀ := by rw [invT_val, inv_inv]
  have hMK : invT u⁻¹ ∈ KO k A := invT_mem_KO (inv_mem hu)
  have hdep : HasDepth ϖ e (blockLat ϖ e (Assignment.two.block D₁ D₂))
      (phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    have h1 := (FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e (Assignment.one.block D₁ D₂) hϖ hψ).1 Φ hΦ
    have h2 := @FrameDepth.hasDepth_phiA k _ _ _ _ _ _ A A' (D₁ ⊕ D₂) _ _ _ _ _ _ μ (by assumption) σ ν ϖ e
      (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν h1
    rw [← compl_block_one, ← latA_blockLat]; exact h2
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hφu : ∀ Y, (ν (gdet u) : ℂ) * phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) (u.valᵀ * Y) =
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ) Y := by
    intro Y
    classical
    rw [phiA, phiA, ← hM, GlobalTheory.PrimFrameLeft.isPrimFrame_gl_mul_iff _ _ hMK]
    by_cases hY : IsPrimFrame (latA ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))) Y
    · rw [if_pos hY, if_pos hY]
      obtain ⟨h, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hY.1
      rw [hM]
      exact GlobalTheory.T.frameTestFunction_transpose_integralGL_mul_eq_char μ σ ν _ u hu h
    · rw [if_neg hY, if_neg hY, mul_zero]
  have hb : ∀ (Q : D₁ ⊕ D₂ → Prop), (∀ j ∈ Assignment.two.block D₁ D₂, Q j) ↔ ∀ c, Q (Sum.inr c) := by
    intro Q
    refine ⟨fun h c => h _ (by simp [Assignment.block]), fun h j hj => ?_⟩
    cases j with
    | inl c => simp [Assignment.block] at hj
    | inr c => exact h c
  set X' : Matrix A (D₁ ⊕ D₂) k := fromCols (u.valᵀ * X.toCols₁) ((u⁻¹).val * X.toCols₂) with hX'
  have hcond : (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X' i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]) := by
    simp only [hb]
    have := mul_mul_mem_matLat_iff (inv_mem hu) (one_mem (KO k D₂)) X.toCols₂
    rw [mem_matLat_stdLat, mem_matLat_stdLat, Units.val_one, Matrix.mul_one] at this
    simpa [hX', Matrix.toCols₂] using this
  have hset : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      setCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) =
        u.valᵀ * setCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [hM]
    ext i j
    rcases j with c | c
    · simp [setCols, Assignment.block, hX', Matrix.mul_apply, Matrix.toCols₁]
    · simp [setCols, Assignment.block, Matrix.mul_apply]
      first | rfl | exact Matrix.mul_apply | (erw [Matrix.mul_apply]; simp)
  have hsub : X'.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) =
      (u⁻¹).val * X.submatrix id (Subtype.val : Assignment.two.block D₁ D₂ → D₁ ⊕ D₂) := by
    ext i ⟨j, hj⟩
    rcases j with c | c
    · simp [Assignment.block] at hj
    · simp [hX', Matrix.mul_apply, Matrix.toCols₂]
  have hpair : ∀ Z : Matrix A (Assignment.two.block D₁ D₂) k,
      pairCols (Assignment.two.block D₁ D₂) X' ((invT u⁻¹).val * Z) = pairCols (Assignment.two.block D₁ D₂) X Z := by
    intro Z
    rw [pairCols_eq_trace, pairCols_eq_trace, hsub, hM, transpose_mul, ← Matrix.mul_assoc, trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul]
  unfold squareFlip
  rw [compl_block_one, invFourierSum_inv_apply, invFourierSum_inv_apply]
  by_cases hX : ∀ i, ∀ j ∈ Assignment.two.block D₁ D₂, X i j ∈ 𝒪[k]
  · rw [if_pos hX, if_pos (hcond.2 hX)]
    set φ := phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
    have hg : ∀ Z Z' : Matrix A (Assignment.two.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) →
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) (Z + Z') =
        (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) Z := by
      intro Z Z' hZ'
      have e1 : setCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          setCols (Assignment.two.block D₁ D₂) X' Z + setCols (Assignment.two.block D₁ D₂) 0 Z' := by
        ext i j; by_cases h : j ∈ Assignment.two.block D₁ D₂ <;> simp [setCols, h]
      have e2 : pairCols (Assignment.two.block D₁ D₂) X' (Z + Z') =
          pairCols (Assignment.two.block D₁ D₂) X' Z + pairCols (Assignment.two.block D₁ D₂) X' Z' := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      have e3 : pairCols (Assignment.two.block D₁ D₂) X' Z' ∈ 𝒪[k] :=
        Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (hZ' i j) (hcond.2 hX i j j.2)
      simp only
      rw [e1, e2, hdep.2, AddChar.map_add_eq_mul, triv _ e3, mul_one]
      apply FourierDepth.mem_matLat_smul_blockLat.2
      constructor
      · intro i j hj
        simpa [setCols, hj] using hZ' i ⟨j, hj⟩
      · intro i j hj
        simp [setCols, hj]
    have key := GlobalTheory.T.sum_quotientIntegerMatrices_invariant_integralGL_mul_left ϖ e hϖ (fun Z => φ (setCols (Assignment.two.block D₁ D₂) X' Z) * (ψ (pairCols (Assignment.two.block D₁ D₂) X' Z) : ℂ)) hg (invT u⁻¹) hMK
    beta_reduce at key
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hset, hpair, ← mul_assoc, hφu]
  · rw [if_neg hX, if_neg (mt hcond.1 hX), mul_zero]

end GlobalTheory.SquareFlipRows
