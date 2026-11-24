module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.GKQuot

variable {p q : ℕ}

def quotAct (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    Mat p q →ₗ[ℂ] Module.End ℂ (M.V ⧸ N) where
  toFun Z := N.mapQ N (M.act Z) (hN Z)
  map_add' Z W := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_smul' c Z := by
    apply Submodule.linearMap_qext
    ext x
    simp

theorem quotAct_mk (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z))
    (Z : Mat p q) (x : M.V) : quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := rfl

def quotMod (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    GKMod p q where
  V := M.V ⧸ N
  act := quotAct M N hN
  lie X Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [quotAct_mk, M.lie X Y]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, quotAct_mk, map_sub]
  kfin v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    obtain ⟨W, hW, hx, hK⟩ := M.kfin x
    refine ⟨W.map N.mkQ, inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [quotAct_mk]
    exact Submodule.mem_map_of_mem (hK X hX w hw)
  wts v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (quotAct M N hN) μ).comap N.mkQ := by
      refine iSup_le fun μ y hy => ?_
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro a
      rw [quotAct_mk, ← map_smul, ← map_sub, hy a, map_zero]
    exact h (M.wts x)

theorem exists_unitary_quotient (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H)
    (hE : ∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) :
    ∃ (A : UGKMod p q) (f : M.V →ₗ[ℂ] A.M.V) (Eb : A.M.V →ₗ[ℂ] H), Function.Surjective f ∧
      Function.Injective Eb ∧ (∀ x, Eb (f x) = E x) ∧ ∀ Z x, f (M.act Z x) = A.M.act Z (f x) := by

  let N : Submodule ℂ M.V := LinearMap.ker E
  have hN : ∀ Z, N ≤ N.comap (M.act Z) := by
    intro Z x hx
    have hx' : E x = 0 := hx
    show E (M.act Z x) = 0
    have h := hE Z x (M.act Z x)
    rw [hx', inner_zero_left] at h
    exact inner_self_eq_zero.mp h

  let Eb : M.V ⧸ N →ₗ[ℂ] H := N.liftQ E le_rfl
  have hEb : ∀ x, Eb (N.mkQ x) = E x := fun x => N.liftQ_apply E x
  have hinj : Function.Injective Eb := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [LinearMap.mem_ker, hEb] at hv
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr hv
  have hact : ∀ Z x, quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := quotAct_mk M N hN

  let ip : M.V ⧸ N →ₗ⋆[ℂ] M.V ⧸ N →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp Eb).compl₂ Eb
  let A : UGKMod p q :=
    { M := quotMod M N hN
      ip := ip
      herm := by
        intro v w
        show star (inner ℂ (Eb v) (Eb w)) = inner ℂ (Eb w) (Eb v)
        exact inner_conj_symm (Eb w) (Eb v)
      pos := by
        intro v hv
        have hne : Eb v ≠ 0 := fun h0 => hv (hinj (h0.trans (map_zero Eb).symm))
        have h : 0 < RCLike.re (inner ℂ (Eb v) (Eb v)) := by
          rw [inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hne) 2
        show 0 < (inner ℂ (Eb v) (Eb v)).re
        exact h
      adj := by
        intro Z v w
        obtain ⟨x, rfl⟩ := N.mkQ_surjective v
        obtain ⟨y, rfl⟩ := N.mkQ_surjective w
        show inner ℂ (Eb (quotAct M N hN Z (N.mkQ x))) (Eb (N.mkQ y)) =
          inner ℂ (Eb (N.mkQ x)) (Eb (quotAct M N hN (adjZ Z) (N.mkQ y)))
        rw [hact, hact, hEb, hEb, hEb, hEb]
        exact hE Z x y }
  exact ⟨A, N.mkQ, Eb, N.mkQ_surjective, hinj, hEb, fun Z x => (hact Z x).symm⟩

end GlobalTheory.GKQuot
