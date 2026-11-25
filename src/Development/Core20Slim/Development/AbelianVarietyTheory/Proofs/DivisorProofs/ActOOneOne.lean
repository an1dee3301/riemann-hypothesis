module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblBox

open Formalism.IndefR.Datum

variable {D : D7} {S T : HSp D}

def top (w : WO S (GlobalTheory.Doubling.dblSp T)) : WO S T := w.submatrix (finSumFinEquiv ∘ Sum.inl) id

def bot (w : WO S (GlobalTheory.Doubling.dblSp T)) : WO S T := w.submatrix (finSumFinEquiv ∘ Sum.inr) id

def join (u v : WO S T) : WO S (GlobalTheory.Doubling.dblSp T) := (Matrix.fromRows u v).submatrix finSumFinEquiv.symm id

@[simp] theorem top_join (u v : WO S T) : top (join u v) = u := by
  ext i j
  simp only [top, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, id]

@[simp] theorem bot_join (u v : WO S T) : bot (join u v) = v := by
  ext i j
  simp only [bot, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr, id]

theorem join_top_bot (w : WO S (GlobalTheory.Doubling.dblSp T)) : join (top w) (bot w) = w := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp only [top, bot, join, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id]

@[simp] theorem top_add (x y : WO S (GlobalTheory.Doubling.dblSp T)) : top (x + y) = top x + top y := rfl
@[simp] theorem bot_add (x y : WO S (GlobalTheory.Doubling.dblSp T)) : bot (x + y) = bot x + bot y := rfl

def box (f₁ f₂ : WO S T → ℂ) : WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun w => f₁ (top w) * star (f₂ (bot w))

theorem hO_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    hO S (GlobalTheory.Doubling.dblSp T) x y = hO S T (top x) (top y) - hO S T (bot x) (bot y) := by
  simp only [hO, GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, map_zero, map_neg, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    top, bot, Function.comp_apply, id]
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem symplO_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    symplO S (GlobalTheory.Doubling.dblSp T) x y = symplO S T (top x) (top y) - symplO S T (bot x) (bot y) := by
  simp only [symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_dbl (x y : WO S (GlobalTheory.Doubling.dblSp T)) :
    symplOH S (GlobalTheory.Doubling.dblSp T) x y = symplOH S T (top x) (top y) - symplOH S T (bot x) (bot y) := by
  simp only [symplOH, symplO_dbl, mul_sub]

def IsTopDiag (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)) : Prop :=
  Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1)

theorem top_actO {h : GA D T} {hd : GA D (GlobalTheory.Doubling.dblSp T)} (hh : IsTopDiag h hd) (g : GA D S)
    (w : WO S (GlobalTheory.Doubling.dblSp T)) : top (actO S (GlobalTheory.Doubling.dblSp T) g hd w) = actO S T g h (top w) := by
  ext i j
  simp only [top, actO, IsTopDiag] at hh ⊢
  rw [hh]
  simp only [Matrix.submatrix_apply, Function.comp_apply, id, Matrix.mul_apply, Matrix.reindex_apply,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem bot_actO {h : GA D T} {hd : GA D (GlobalTheory.Doubling.dblSp T)} (hh : IsTopDiag h hd) (g : GA D S)
    (w : WO S (GlobalTheory.Doubling.dblSp T)) : bot (actO S (GlobalTheory.Doubling.dblSp T) g hd w) = actO S T g 1 (bot w) := by
  ext i j
  simp only [bot, actO, IsTopDiag] at hh ⊢
  rw [hh]
  simp only [Matrix.submatrix_apply, Function.comp_apply, id, Matrix.mul_apply, Matrix.reindex_apply,
    ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  rw [show Formalism.L2.Theta.mt T 1 = 1 from rfl]

theorem actO_one_one (w : WO S T) : actO S T 1 1 w = w := by
  simp only [actO, inv_one, show Formalism.L2.Theta.mt T 1 = 1 from rfl, show Formalism.L2.Theta.mt S 1 = 1 from rfl,
    Matrix.one_mul, Matrix.mul_one]

theorem psi_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (b : AF D.host.F) : ψ (-b) = star (ψ b) := by
  have h1 : ψ (-b) * ψ b = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 := GlobalTheory.ThetaSchur.mul_star_psi hψ b
  linear_combination (-ψ (-b)) * h2 + star (ψ b) * h1

theorem heisO_box {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (w : WO S (GlobalTheory.Doubling.dblSp T))
    (f₁ f₂ : WO S T → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.dblSp T) w (box f₁ f₂) = box (heisO ψ S T (top w) f₁) (heisO ψ S T (bot w) f₂) := by
  funext x
  simp only [heisO, box, symplOH_dbl, top_add, bot_add, sub_eq_add_neg, AddChar.map_add_eq_mul, psi_neg hψ, star_mul']
  ring

end GlobalTheory.DblBox
