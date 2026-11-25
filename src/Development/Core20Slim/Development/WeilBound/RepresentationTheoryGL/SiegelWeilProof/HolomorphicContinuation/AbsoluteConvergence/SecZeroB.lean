module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZeroA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
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
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Filter Topology Set Polynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def lowM (n : ℕ) (s : ℝ) : M2 n := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1

lemma lowM_mul (s s' : ℝ) : lowM n s * lowM n s' = lowM n (s + s') := by
  simp only [lowM, fromBlocks_multiply]
  simp [add_smul]

lemma lowM_zero : lowM n 0 = 1 := by
  unfold lowM; simp [fromBlocks_one]

def lowU (n : ℕ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨lowM n s, lowM n (-s), by rw [lowM_mul, add_neg_cancel, lowM_zero], by rw [lowM_mul, neg_add_cancel, lowM_zero]⟩

def lowG (n : ℕ) (s : ℝ) : GR n := ⟨lowU n s, InG_lower s⟩

lemma lowG_cont : Continuous (lowG n) := by
  unfold lowG
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have hc : Continuous (fun s : ℝ => lowM n s) := by
    unfold lowM
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      (Complex.continuous_ofReal.smul continuous_const) continuous_const
  exact ⟨hc, hc.comp continuous_neg⟩

lemma lowG_zero : lowG n 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact lowM_zero

lemma mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

lemma lower_left_block_lowering_mul (y : GR n) (s : ℝ) :
    (mR (y * lowG n s)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (s : ℂ) • (mR y).toBlocks₂₂ := by
  rw [mR_mul]
  show (mR y * lowM n s).toBlocks₂₁ = _
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  unfold lowM
  rw [fromBlocks_multiply]
  simp

lemma dense_cell (y : GR n) : y ∈ closure {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, C = (mR y).toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (mR y).toBlocks₂₂ := ⟨_, rfl⟩
  have hG : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hgg : mR y * mR y⁻¹ = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    rfl
  have hJJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply]
    simp [← fromBlocks_one, fromBlocks_neg]
  have key : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have h1 : (mR y)ᴴ * JJ n = JJ n * mR y⁻¹ := by
      calc (mR y)ᴴ * JJ n = (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hgg, Matrix.mul_one]
        _ = ((mR y)ᴴ * JJ n * mR y) * mR y⁻¹ := by simp only [Matrix.mul_assoc]
        _ = JJ n * mR y⁻¹ := by rw [hG]
    calc mR y * JJ n * (mR y)ᴴ = mR y * JJ n * (mR y)ᴴ * (JJ n * JJ n) * (-1) := by
          rw [hJJ]; simp
      _ = mR y * JJ n * ((mR y)ᴴ * JJ n) * JJ n * (-1) := by simp only [Matrix.mul_assoc]
      _ = mR y * (JJ n * JJ n) * mR y⁻¹ * JJ n * (-1) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = JJ n := by
          rw [hJJ]
          simp [hgg]
  have hherm : C * Dᴴ = D * Cᴴ := by
    have hb := congrArg Matrix.toBlocks₂₂ key
    rw [← fromBlocks_toBlocks (mR y), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at hb
    simp at hb
    rw [← hC, ← hD] at hb
    exact (neg_add_eq_zero.mp hb).symm
  have hpos : ((C * Cᴴ + D * Dᴴ).det) ≠ 0 := by
    have hu : IsUnit (mR y) := ⟨(y : GL (Fin n ⊕ Fin n) ℂ), rfl⟩
    open ComplexOrder in
    have hpd : ((mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr).PosDef :=
      (Matrix.PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_iff_isUnit.mpr hu)).submatrix Sum.inr_injective
    have he : (mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr = C * Cᴴ + D * Dᴴ := by
      change Matrix.toBlocks₂₂ (mR y * (mR y)ᴴ) = _
      rw [hC, hD]
      conv_lhs => rw [← fromBlocks_toBlocks (mR y), fromBlocks_conjTranspose, fromBlocks_multiply]
      simp
    rw [← he]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit |>.ne_zero
  have hprod : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = C * Cᴴ + D * Dᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [← hherm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have hI : (C + Complex.I • D).det ≠ 0 := by
    intro h
    apply hpos
    rw [← hprod, Matrix.det_mul, h, zero_mul]
  let P : Polynomial ℂ :=
    Matrix.det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  have hev : ∀ r : ℂ, P.eval r = (C + r • D).det := by
    intro r
    show Polynomial.evalRingHom r (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP : P ≠ 0 := fun h => hI (by rw [← hev, h, Polynomial.eval_zero])
  have hfin : {s : ℝ | P.eval (s : ℂ) = 0}.Finite := by
    apply Set.Finite.subset ((P.roots.toFinset.finite_toSet).preimage
      Complex.ofReal_injective.injOn)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp [Polynomial.mem_roots hP, hs]
  have hT : Tendsto (fun s : ℝ => y * lowG n s) (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    have h0 : Tendsto (fun s : ℝ => y * lowG n s) (𝓝 0) (𝓝 (y * lowG n 0)) :=
      (continuous_const.mul lowG_cont).tendsto 0
    rw [lowG_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hT
  have hopen : ({s : ℝ | P.eval (s : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs0
  show ((mR (y * lowG n s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_lowering_mul, ← hC, ← hD, ← hev]
  intro h
  exact hs ⟨h, hs0⟩

end PositivityTheory.Rg.Sw.AbsSt.SZ
