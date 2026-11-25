module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Option.Instances
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.PEquiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.ColumnRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]

def permGL (π : C ≃ C) : GL C k :=
  ⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in
theorem frameMatrixFirstColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    X0 k σ' * (invT h).val = X0 k σ * (invT (permGL (σ.symm.trans σ') * h)).val := by
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, invT_val, invT_val, _root_.mul_inv_rev]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul, Option.mem_def, Equiv.symm_apply_eq]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in
theorem frameMatrixSecondColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    Y0 k σ * (permGL (σ.symm.trans σ') * h).val = Y0 k σ' * h.val := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul]

variable [MeasurableSpace k] [BorelSpace k]

theorem fFun_renumber (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k) :
    fFun μ σ' ν Ψ X = ((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹ * fFun μ σ ν Ψ X := by
  set Q : GL C k := permGL (σ.symm.trans σ') with hQ
  by_cases hX : ∃ h : GL C k, X = X0 k σ' * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have hc : (ν (gdet Q) : ℂ) * apow (gdet Q) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    rw [splitTheta_fFun_frameFirstBlock_mul μ σ', frameMatrixFirstColumnBlock_renumber σ σ' h, splitTheta_fFun_frameFirstBlock_mul μ σ, ← hQ, frameMatrixSecondColumnBlock_renumber, gdet_mul, map_mul, apow_mul,
      Units.val_mul]
    have ha := apow_ne_zero (gdet Q) ((Fintype.card C : ℂ) / 2)
    have hn : (ν (gdet Q) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hX' : ¬ ∃ h : GL C k, X = X0 k σ * (invT h).val := fun H =>
      hX ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ' X).1 ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 H))
    rw [fFun, dite_eq_right hX, fFun, dite_eq_right hX', mul_zero]

end GlobalTheory.ColumnRenumber


open GlobalTheory.ColumnRenumber in
theorem GlobalTheory.ColumnRenumber.phiA_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  intro k _ _ _ _ _ _ A A' C _ _ _ _ _ _ μ _ σ σ' ν
  refine ⟨((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹,
    inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)), fun ϖ n Λ Ψ X => ?_⟩
  unfold phiA
  split_ifs
  · exact fFun_renumber μ σ σ' ν Ψ X
  · rw [mul_zero]
