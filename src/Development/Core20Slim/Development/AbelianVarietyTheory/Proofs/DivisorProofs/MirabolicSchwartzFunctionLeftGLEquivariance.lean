module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
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

namespace GlobalTheory

theorem fFun_mul_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k),
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν Ψ g h
  let f : Matrix (Fin a) (Fin a) k →* Matrix C C k :=
    { toFun := fun M => (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm
      map_one' := by rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
      map_mul' := fun M N => by
        rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp }
  let E : GL C k := Units.map f g
  have hE : ∀ M : Matrix (Fin a) (Fin a) k, f M = (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm := fun _ => rfl
  have hX : g.val * X0 k σ = X0 k σ * E.val := by
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [X0, E, hE, Matrix.mul_apply]
  have hY : Y0 k σ * (invT E).val = Y0 k σ := by
    ext i j
    rw [frameMatrixSecondColumnBlock_mul_apply, invT_val]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [Y0, E, hE, ← map_inv, Matrix.one_apply, eq_comm]
  have hdet : gdet E = gdet g := by
    ext
    simp [E, hE, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have h1 : g.val * (X0 k σ * (invT h).val) = X0 k σ * (invT (invT E * h)).val := by
    rw [map_mul, invT_invT, Units.val_mul, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  have h2 : Y0 k σ * (invT E * h).val = Y0 k σ * h.val := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hY]
  have h3 : gdet (invT E * h) = (gdet g)⁻¹ * gdet h := by rw [gdet_mul, gdet_invT, hdet]
  rw [h1, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, h2, h3, map_mul, map_inv, apow_mul, apow_inv, apow_neg,
    Units.val_mul, Units.val_inv_eq_inv_val]
  have hν : ((ν (gdet g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have ha : apow (gdet g) ((Fintype.card C : ℂ) / 2) ≠ 0 := apow_ne_zero _ _
  field_simp

end GlobalTheory
