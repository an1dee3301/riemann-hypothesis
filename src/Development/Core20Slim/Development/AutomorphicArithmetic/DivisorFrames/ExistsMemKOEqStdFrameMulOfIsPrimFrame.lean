module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Classical
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) (X : Matrix A D k), IsPrimFrame (stdLat k D) X → ∃ u ∈ KO k D, X = X0 k σ * (invT u).val := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ X hX
  obtain ⟨R, hR, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let R' : Matrix D A 𝒪[k] := Matrix.of fun i j => ⟨R i j, hR i j⟩
  have h1 : X' * R' = 1 := by
    apply Matrix.map_injective (f := algebraMap 𝒪[k] k) Subtype.val_injective
    show (X' * R').map (algebraMap 𝒪[k] k) = (1 : Matrix A A 𝒪[k]).map (algebraMap 𝒪[k] k)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hXR
  let ρ := IsLocalRing.residue 𝒪[k]
  have h2 : X'.map ρ * R'.map ρ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : (X'.map ρ).rank = Fintype.card A := by
    refine le_antisymm (Matrix.rank_le_card_height _) ?_
    have := Matrix.rank_mul_le_left (X'.map ρ) (R'.map ρ)
    rwa [h2, Matrix.rank_one] at this
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ _).1 h3
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let C : Matrix D D 𝒪[k] := Matrix.of fun r j =>
    Sum.elim (fun i => X' i j) (fun i => l ((invT h).val (σ (Sum.inr i)) j)) (σ.symm r)
  have h4 : ρ.mapMatrix C = (invT h).val := by
    ext r j
    obtain ⟨i | i, rfl⟩ := σ.surjective r
    · have := congrFun (congrFun hh i) j
      rw [frameMatrixFirstColumnBlock_mul_apply] at this
      simpa [C] using this
    · simp [C, ρ, hl]
  have hK : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    rw [show (IsLocalRing.residue 𝒪[k]).mapMatrix C = _ from h4]
    exact (invT h).det_ne_zero
  obtain ⟨w, hw⟩ := hK
  refine ⟨invT (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w), invT_mem_KO ⟨w, rfl⟩, ?_⟩
  rw [invT_invT]
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply]
  show _ = ((w.val (σ (Sum.inl i)) j : 𝒪[k]) : k)
  rw [hw]
  simp [C, X']
