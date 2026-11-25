module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem resAlg_of_isUnrQuad : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  intro R _ σ ϖ q ε h
  have hτ : ∀ a : R, barσ σ ϖ h.fix_ϖ 1 (Ideal.Quotient.mk (lev ϖ 1) a) =
      Ideal.Quotient.mk (lev ϖ 1) (σ a) := fun a => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨u, hu, hdec⟩ := h.basis
  refine ⟨?_, ?_, ?_, h.one_lt, h.card, h.eps⟩
  · intro e
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    rw [hτ a, hτ (σ a), h.inv]
  · intro e he hne
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
    rw [hτ] at he
    have hy0 : Ideal.Quotient.mk (lev ϖ 1) y = 0 := by
      have h1 : Ideal.Quotient.mk (lev ϖ 1) (y * (u - σ u)) = 0 := by
        have hxy : y * (u - σ u) = (x + y * u) - σ (x + y * u) := by
          rw [map_add (f := _), map_mul, hx, hy]
          ring
        rw [hxy, map_sub, he, sub_self]
      rw [map_mul] at h1
      exact (IsUnit.mul_left_eq_zero (hu.map (Ideal.Quotient.mk (lev ϖ 1)))).mp h1
    have hxe : Ideal.Quotient.mk (lev ϖ 1) (x + y * u) = Ideal.Quotient.mk (lev ϖ 1) x := by
      rw [map_add (f := _), map_mul, hy0, zero_mul, add_zero]
    rw [hxe] at hne ⊢
    exact (h.fixLocal x hx fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)).map _
  · refine ⟨Ideal.Quotient.mk (lev ϖ 1) u, ?_, ?_⟩
    · have hm := hu.map (Ideal.Quotient.mk (lev ϖ 1))
      rwa [map_sub, ← hτ] at hm
    · intro e
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
      obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
      refine ⟨Ideal.Quotient.mk (lev ϖ 1) x, Ideal.Quotient.mk (lev ϖ 1) y, ?_, ?_, ?_⟩
      · rw [hτ, hx]
      · rw [hτ, hy]
      · rw [map_add (f := _), map_mul]

end GlobalTheory.CompanionTheory.UnrDens
