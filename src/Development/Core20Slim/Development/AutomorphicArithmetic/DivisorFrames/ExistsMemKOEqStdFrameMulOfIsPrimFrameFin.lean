module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLMulIsPrimitiveFrameDiagonalLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
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
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

open Matrix in
theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame_fin :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {a' : ℕ} (σ : A ⊕ Fin a' ≃ D) (X : Matrix A D k), IsPrimFrame (GlobalTheory.SplitFlip.stdLat k D) X → ∃ κ ∈ GlobalTheory.SplitWeil.KO k D, X = X0 k σ * (invT κ).val := by
  intro k _ _ _ _ A D _ _ _ _ a' σ X hX
  have hXint : ∀ i j, X i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hX.2.1
  obtain ⟨R, hRint, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
  set Y : Matrix (Fin a') D k := Y0 k σ * (h : Matrix D D k) with hYeq
  have hYX : Y * X.transpose = 0 := by
    rw [hh]
    exact frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero σ h
  have hYrank : Y.rank = a' := by
    have hY0 : Y0 k σ * (Y0 k σ).transpose = 1 := by
      ext i j
      simp [Y0, Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq']
    have hW : Y * (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose) = 1 := by
      rw [hYeq, Matrix.mul_assoc, ← Matrix.mul_assoc (h : Matrix D D k), ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.one_mul, hY0]
    have h1 := Matrix.rank_mul_le_left Y (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose)
    rw [hW, Matrix.rank_one, Fintype.card_fin] at h1
    have h2 := Matrix.rank_le_card_height Y
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame k a' D (fun _ => 1) Y hYrank
  set Y' : Matrix (Fin a') D k := (g₀ : Matrix (Fin a') (Fin a') k) * Y with hY'eq
  have hY'prim : IsPrimFrame (stdLat k D) Y' := hg₀
  have hY'int : ∀ i j, Y' i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hY'prim.2.1
  obtain ⟨S, hSint, hY'S⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hY'prim
  have hY'X : Y' * X.transpose = 0 := by
    rw [hY'eq, Matrix.mul_assoc, hYX, Matrix.mul_zero]
  have hRX : R.transpose * X.transpose = 1 := by
    rw [← Matrix.transpose_mul, hXR, Matrix.transpose_one]
  set S' : Matrix D (Fin a') k := S - X.transpose * (R.transpose * S) with hS'eq
  have hRS' : R.transpose * S' = 0 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hRX, Matrix.one_mul, sub_self]
  have hY'S' : Y' * S' = 1 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hY'X, Matrix.zero_mul, sub_zero, hY'S]
  have mulInt : ∀ {m n o : Type} [Fintype n] (P : Matrix m n k) (Q : Matrix n o k),
      (∀ i j, P i j ∈ 𝒪[k]) → (∀ i j, Q i j ∈ 𝒪[k]) → ∀ i j, (P * Q) i j ∈ 𝒪[k] := by
    intro m n o _ P Q hP hQ i j
    rw [Matrix.mul_apply]
    exact sum_mem fun x _ => mul_mem (hP _ _) (hQ _ _)
  have hS'int : ∀ i j, S' i j ∈ 𝒪[k] := by
    intro i j
    rw [hS'eq, Matrix.sub_apply]
    refine sub_mem (hSint i j) ?_
    exact mulInt _ _ (fun a b => hXint b a) (mulInt _ _ (fun a b => hRint b a) hSint) i j
  let K : Matrix D D k := (Matrix.fromRows R.transpose Y').submatrix σ.symm (Equiv.refl D)
  let N : Matrix D D k := (Matrix.fromCols X.transpose S').submatrix (Equiv.refl D) σ.symm
  have hKN : K * N = 1 := by
    simp only [K, N]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromRows_mul_fromCols, hRX, hRS', hY'X, hY'S',
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hNK : N * K = 1 := mul_eq_one_comm.1 hKN
  let κ : GL D k := ⟨K, N, hKN, hNK⟩
  refine ⟨κ, ?_, ?_⟩
  · rw [mem_KO_iff]
    constructor
    · intro e d
      show K e d ∈ 𝒪[k]
      simp only [K, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hRint d i
      · simpa using hY'int j d
    · intro d e
      show N d e ∈ 𝒪[k]
      simp only [N, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hXint i d
      · simpa using hS'int d j
  · ext i d
    rw [frameMatrixFirstColumnBlock_mul_apply]
    show X i d = N d (σ (Sum.inl i))
    simp [N]
