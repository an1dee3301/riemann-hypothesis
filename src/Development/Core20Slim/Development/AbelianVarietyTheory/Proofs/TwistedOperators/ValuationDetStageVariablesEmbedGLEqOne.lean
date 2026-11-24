module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepLin
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

def splitVar {n m σ : Type} (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s) :
    (n × {s // Q s}) ⊕ {ls : m × σ // P (Sum.inr ls.1, ls.2)} ≃ {rs // P rs} where
  toFun := Sum.elim (fun a => ⟨(Sum.inl a.1, a.2.1), (h _ _).2 a.2.2⟩) (fun a => ⟨(Sum.inr a.1.1, a.1.2), a.2⟩)
  invFun := fun a => match a with
    | ⟨(Sum.inl r, s), hs⟩ => Sum.inl (r, ⟨s, (h _ _).1 hs⟩)
    | ⟨(Sum.inr l, s), hs⟩ => Sum.inr ⟨(l, s), hs⟩
  left_inv := by rintro (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rfl
  right_inv := by rintro ⟨⟨r | r, s⟩, hs⟩ <;> rfl

theorem det_colwise_fromBlocks {k : Type} [CommRing k] {n m σ : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype σ] (P : (n ⊕ m) × σ → Prop) (Q : σ → Prop) (h : ∀ r s, P (Sum.inl r, s) ↔ Q s)
    [Fintype {rs // P rs}] [DecidableEq {rs // P rs}] (κ : Matrix n n k)
    (M : Matrix {rs // P rs} {rs // P rs} k)
    (hM : ∀ a b, M a b = if a.1.2 = b.1.2 then (fromBlocks κ 0 0 1 : Matrix (n ⊕ m) (n ⊕ m) k) a.1.1 b.1.1 else 0) :
    M.det = κ.det ^ Fintype.card {s // Q s} := by
  rw [← det_submatrix_equiv_self (splitVar P Q h) M]
  have : M.submatrix (splitVar P Q h) (splitVar P Q h) =
      fromBlocks (blockDiagonal fun _ : {s // Q s} => κ) 0 0 1 := by
    ext a b
    rcases a with (⟨r, s, hs⟩ | ⟨⟨l, s⟩, hs⟩) <;> rcases b with (⟨r', s', hs'⟩ | ⟨⟨l', s'⟩, hs'⟩) <;>
      simp [hM, splitVar, blockDiagonal_apply, one_apply]
    by_cases h1 : s = s' <;> by_cases h2 : l = l' <;> simp [h1, h2, Matrix.one_apply, Subtype.ext_iff]
  rw [this, det_fromBlocks_zero₂₁, det_blockDiagonal]
  simp

theorem valuation_det_stepLin_embX : ∀ {k : Type} [Field k] [ValuativeRel k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (κ : GL n k), valuation k (gdet κ : k) = 1 → valuation k (stepLin n' (embX c κ).val).det = 1 := by
  intro k _ _ n n' _ _ _ _ c κ hκ
  let Q : n' ⊕ Fin (c + 1) → Prop := Sum.elim (fun _ => False)
    (fun i => c / 2 + 1 < i.val + 1 ∨ (Even c ∧ i.val = c / 2))
  have h : ∀ (r : n) s, (Free (c := c) (c / 2 + 1) (Sum.inl r, s) ∨ Kept (c := c) (Sum.inl r, s)) ↔ Q s := by
    rintro r (s | s) <;> simp [Q, Free, Kept]
  rw [det_colwise_fromBlocks (fun rs => Free (c / 2 + 1) rs ∨ Kept rs) Q h κ.val _ (fun a b => by
    simp only [stepLin, of_apply]; split_ifs <;> rfl), map_pow]
  have : valuation k κ.val.det = 1 := hκ
  rw [this, one_pow]

end GlobalTheory.StepLeft
