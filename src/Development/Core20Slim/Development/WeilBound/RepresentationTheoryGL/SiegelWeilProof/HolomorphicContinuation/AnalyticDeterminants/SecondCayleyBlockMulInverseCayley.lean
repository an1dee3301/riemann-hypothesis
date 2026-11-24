module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContinuousOnIteratedFDerivTranslate
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Cmi (n : ℕ) : M2 n :=
  fromBlocks ((-Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1) ((Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1)

theorem cm_mul_cmi : Cm n * Cmi n = 1 := by
  rw [Cm, Cmi, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases h : i = j <;>
    simp [Matrix.one_apply, h, Matrix.add_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

theorem cm_inv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv cm_mul_cmi

theorem toBlocks₂₁_mul (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₂₂_mul (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₂₁ (x : M2 n) : (x * Cm n).toBlocks₂₁ = u1 x := by
  rw [toBlocks₂₁_mul, u1, Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one]

theorem mul_cm₂₂ (x : M2 n) : (x * Cm n).toBlocks₂₂ = u2 x := by
  rw [toBlocks₂₂_mul, u2, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one]

theorem first_cayley_block_mul_inverse_cayley (y : M2 n) : u1 (y * Cmi n) = y.toBlocks₂₁ := by
  rw [u1, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem second_cayley_block_mul_inverse_cayley (y : M2 n) : u2 (y * Cmi n) = y.toBlocks₂₂ := by
  rw [u2, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem uAct : UAct := by
  intro n x P Q R S
  simp only [mX, cm_inv, ← Matrix.mul_assoc]
  rw [first_cayley_block_mul_inverse_cayley, second_cayley_block_mul_inverse_cayley, toBlocks₂₁_mul (x * Cm n) (fromBlocks P Q R S),
    toBlocks₂₂_mul (x * Cm n) (fromBlocks P Q R S), mul_cm₂₁, mul_cm₂₂]
  simp

def incl (s : Finset (Fin n)) : Matrix (Fin n) s ℂ := Matrix.of fun c i => if c = (i : Fin n) then 1 else 0

def subOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix s s ℂ :=
  M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))

theorem minorOn_eq (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : minorOn s M = (subOn s M).det := rfl

theorem sum_incl (s : Finset (Fin n)) (a : Fin n) (f : s → ℂ) :
    ∑ i : s, (if a = (i : Fin n) then (1 : ℂ) else 0) * f i = if h : a ∈ s then f ⟨a, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro i _ hi
      have : a ≠ (i : Fin n) := fun e => hi (Subtype.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : a ≠ (i : Fin n) := fun e => h (e ▸ i.2)
    simp [this]

theorem embOn_eq (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = incl s * T * (incl s)ᵀ := by
  ext a b
  simp only [Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply]
  simp only [sum_incl]
  simp only [mul_comm _ (ite (b = _) _ _)]
  rw [sum_incl]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp [embOn, ha, hb]

theorem incl_mul (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : (incl s)ᵀ * M * incl s = subOn s M := by
  ext i j
  simp [Matrix.mul_apply, incl, subOn, Matrix.transpose_apply]

theorem det_one_add_mul_embOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det = (1 + subOn s M * T).det := by
  rw [embOn_eq]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.det_one_add_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [incl_mul]

theorem detD_const_mul {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) (F : Matrix ι ι ℂ → ℂ) :
    detD (fun S => c * F S) = c * detD F := by
  by_cases hc : c = 0
  · subst hc
    simp [detD]
  · let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc)
    have hfun : (fun S => c * F S) = g ∘ F := by
      funext S
      simp [g, mul_comm]
    unfold detD
    rw [hfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    (simp [g]) <;> ring

theorem card_blkA {j : ℕ} (hj : j ≤ n) : Fintype.card (blkA (n := n) j) = j := by
  rw [Fintype.card_coe, blkA, Fin.card_filter_val_lt, min_eq_right hj]

theorem card_blkB {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by
  rw [Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, card_blkA hj]

theorem scalar_section_mul_block_unipotent {p q : ℤ} {j : ℕ} {x : M2 n} (h1 : (u1 x).det ≠ 0) (h2 : (u2 x).det ≠ 0)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (f0 p q x * (1 + subOn (blkA j) (wM x) * T).det ^ (-q)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ (-p) := by
  have hd1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h1
  have hd2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 h2
  have k1 : u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u1 x * (1 + (wM x)⁻¹ * embOn (blkB j) S) := by
    rw [(uAct n x _ _ _ _).1, wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd2]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd1, Matrix.one_mul,
      Matrix.mul_one]
  have k2 : u2 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u2 x * (1 + wM x * embOn (blkA j) T) := by
    rw [(uAct n x _ _ _ _).2, wM]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd2, Matrix.one_mul,
      Matrix.mul_one]
    abel
  rw [f0, f0, k1, k2, Matrix.det_mul, Matrix.det_mul, det_one_add_mul_embOn, det_one_add_mul_embOn,
    mul_zpow, mul_zpow]
  ring

theorem djSec_of (hC : Cayley) : DjSec := by
  intro n j p q x hj h1 h2
  have hin : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
      (f0 p q x * (∏ i ∈ Finset.range (n - j), (-(p : ℂ) + i)) * minorOn (blkB j) (wM x)⁻¹) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-q) := by
    intro T
    simp_rw [scalar_section_mul_block_unipotent h1 h2 T]
    rw [detD_const_mul, hC, card_blkB hj, minorOn_eq]
    push_cast
    ring
  simp_rw [hin]
  rw [detD_const_mul, hC, card_blkA hj]
  simp only [minorOn_eq]
  push_cast
  ring

end PositivityTheory.Rg.Sw.LVs
