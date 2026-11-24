module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Lemmas
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.Dbl

theorem dblM_gram {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : Cᵀ * N * C.map star = Jm R S) :
    (dblM C)ᵀ * Matrix.fromBlocks N 0 0 (-N) * (dblM C).map star = Jm (R + S) (S + R) := by
  have hG : ∀ a a', ∑ x, (∑ y, C y a * N y x) * (starRingEnd ℂ) (C x a') = Jm R S a a' := by
    intro a a'
    have := congrFun (congrFun h a) a'
    simpa [Matrix.mul_apply] using this
  ext j k
  rcases j with p | p <;> rcases k with q | q <;>
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective p
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective q
    rcases x with r | s <;> rcases y with r' | s' <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, hG, Jm, Formalism.UG.Jpq, Matrix.one_apply,
        Finset.sum_neg_distrib, Matrix.neg_apply, Fin.ext_iff, Function.swap] <;> omega

theorem dblM_rinv {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (h : ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1) :
    ∃ D : Matrix (Ix (R + S) (S + R)) (β ⊕ β) ℂ, dblM C * D = 1 := by
  obtain ⟨C', hC'⟩ := h
  refine ⟨(dblM C'ᵀ)ᵀ, ?_⟩
  have hI : ∀ i i', ∑ r, C i (Sum.inl r) * C' (Sum.inl r) i' + ∑ s, C i (Sum.inr s) * C' (Sum.inr s) i' =
      (1 : Matrix β β ℂ) i i' := by
    intro i i'
    rw [← hC', Matrix.mul_apply, Fintype.sum_sum_type]
  ext i i'
  rcases i with i | i <;> rcases i' with i' | i' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_add, dblM, dblCol, Matrix.one_apply, hI, add_comm, Function.swap]

theorem dblM_isFrame {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : IsFrame N C) : IsFrame (Matrix.fromBlocks N 0 0 (-N)) (dblM C) :=
  ⟨dblM_gram N C h.1, dblM_rinv C h.2⟩

theorem framed_dbl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) :
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  rintro ⟨hab, hA, hC⟩
  refine ⟨hab, hA, fun w => ?_⟩
  have key : b • (dbl JB).map (piInf (τ w)) =
      Matrix.fromBlocks (b • JB.map (piInf (τ w))) 0 0 (-(b • JB.map (piInf (τ w)))) := by
    simp [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_smul, Matrix.map_neg]
  rw [key]
  exact dblM_isFrame _ _ (hC w)

end GlobalTheory.RealLift.Dbl

end
