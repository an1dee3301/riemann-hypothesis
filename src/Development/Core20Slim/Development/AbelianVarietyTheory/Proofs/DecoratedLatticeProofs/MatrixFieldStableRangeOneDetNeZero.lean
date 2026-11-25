module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

open Matrix

namespace GlobalTheory

theorem matrix_stableRange_one (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ)
    (h : c * p + d * q = 1) : ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  classical
  set C := Matrix.toLin' c with hC
  set D := Matrix.toLin' d with hD
  obtain ⟨Wc, hW⟩ := Submodule.exists_isCompl (LinearMap.range D)
  let π := Submodule.linearProjOfIsCompl Wc (LinearMap.range D) hW.symm
  have hdec : ∀ w : Fin n → κ, C (p *ᵥ w) + D (q *ᵥ w) = w := by
    intro w
    simp only [hC, hD, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, h,
      Matrix.one_mulVec]
  have hπD : ∀ v, π (D v) = 0 := by
    intro v
    exact Submodule.linearProjOfIsCompl_apply_right hW.symm ⟨D v, LinearMap.mem_range_self _ _⟩
  have hsurj : Function.Surjective (π ∘ₗ C) := by
    intro w
    refine ⟨p *ᵥ (w : Fin n → κ), ?_⟩
    have h2 : π (w : Fin n → κ) = w := Submodule.linearProjOfIsCompl_apply_left _ w
    have := congrArg π (hdec w)
    rw [map_add (f := _), hπD, add_zero, h2] at this
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (π ∘ₗ C)
    (LinearMap.range_eq_top.mpr hsurj)
  have hdim : Module.finrank κ (LinearMap.ker D) = Module.finrank κ Wc := by
    have h1 := LinearMap.finrank_range_add_finrank_ker D
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker D)
  let projK := Submodule.linearProjOfIsCompl (LinearMap.ker D) K' hK
  let Y : (Fin n → κ) →ₗ[κ] (Fin n → κ) := g ∘ₗ (e : LinearMap.ker D →ₗ[κ] Wc) ∘ₗ projK
  refine ⟨LinearMap.toMatrix' Y, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hM : (c * LinearMap.toMatrix' Y + d) *ᵥ v = C (Y v) + D v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hM] at hv
  have hp : π (C (Y v)) = e (projK v) := by
    have := LinearMap.congr_fun hg (e (projK v))
    simpa [Y] using this
  have h3 : e (projK v) = 0 := by
    have := congrArg π hv
    rwa [map_add, hπD, add_zero, hp, map_zero] at this
  have hk : projK v = 0 := (LinearEquiv.map_eq_zero_iff e).mp h3
  have hY : Y v = 0 := by
    change g (e.toLinearMap (projK v)) = 0
    rw [hk, map_zero]
    exact map_zero g
  have hDv : D v = 0 := by rw [hY, map_zero, zero_add] at hv; exact hv
  have hvK : v ∈ LinearMap.ker D := hDv
  have h4 := Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hvK⟩
  have : (⟨v, hvK⟩ : LinearMap.ker D) = 0 := by rw [← h4]; exact hk
  exact hv0 (congrArg Subtype.val this)

theorem matrix_stableRange_one' : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ),
    c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 :=
  fun κ _ n c d p q h => matrix_stableRange_one κ n c d p q h

end GlobalTheory
