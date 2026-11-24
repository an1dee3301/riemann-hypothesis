module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkewStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := GlobalTheory.T.exists_isotropic_graph_det_ne_zero
  have hlift := GlobalTheory.T.exists_skew_lift_mod_maximalIdeal

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet

end GlobalTheory
