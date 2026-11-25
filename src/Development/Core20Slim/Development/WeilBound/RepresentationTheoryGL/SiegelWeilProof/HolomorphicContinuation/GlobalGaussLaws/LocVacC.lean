module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
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
public import Mathlib.Basic.Real.Star
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
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.ZPow
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Group
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

open Matrix Filter Topology Polynomial
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem inG_JJ : InG (JJ n) := by
  unfold InG
  rw [JJ_conjTranspose, Matrix.mul_assoc, JJ_sq, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem nU_mul (b c : Matrix (Fin n) (Fin n) ℂ) : nU b * nU c = nU (b + c) := by
  simp [nU, fromBlocks_multiply, add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, fromBlocks_one]

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG; simp [nU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, hb.eq]

def jjE : GR n := ⟨⟨JJ n, -JJ n, by rw [Matrix.mul_neg, JJ_sq, neg_neg], by rw [Matrix.neg_mul, JJ_sq, neg_neg]⟩, inG_JJ⟩

def nuE (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : GR n :=
  ⟨⟨nU b, nU (-b), by rw [nU_mul, add_neg_cancel, nU_zero], by rw [nU_mul, neg_add_cancel, nU_zero]⟩, inG_nU hb⟩

def nbar (s : ℝ) : M2 n := fromBlocks 1 0 ((s : ℂ) • 1) 1

theorem nbar_mul (s t : ℝ) : nbar (n := n) s * nbar t = nbar (s + t) := by
  simp [nbar, fromBlocks_multiply, add_smul, add_comm]

theorem nbar_zero : nbar (n := n) 0 = 1 := by simp [nbar, fromBlocks_one]

theorem inG_nbar (s : ℝ) : InG (nbar (n := n) s) := by
  unfold InG
  simp [nbar, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_smul, Complex.conj_ofReal]

def nbE (s : ℝ) : GR n :=
  ⟨⟨nbar s, nbar (-s), by rw [nbar_mul, add_neg_cancel, nbar_zero], by rw [nbar_mul, neg_add_cancel, nbar_zero]⟩, inG_nbar s⟩

theorem nbE_zero : nbE (n := n) 0 = 1 := Subtype.ext (Units.ext nbar_zero)

theorem cont_nbar : Continuous (nbar (n := n)) := by
  unfold nbar
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

theorem cont_nbE : Continuous (nbE (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨cont_nbar, ?_⟩
  exact cont_nbar.comp continuous_neg

theorem lower_left_block_mul_lowering (g : GR n) (s : ℝ) :
    (mR (g * nbE s)).toBlocks₂₁ = (mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂ := by
  rw [mR_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
  show (fromBlocks _ _ _ _ * nbar s).toBlocks₂₁ = _
  simp [nbar, fromBlocks_multiply]

theorem finite_bad (g : GR n) :
    {s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0}.Finite := by
  set C := (mR g).toBlocks₂₁
  set D := (mR g).toBlocks₂₂
  set P : Polynomial ℂ := det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C) with hP
  have hev : ∀ z : ℂ, P.eval z = (C + z • D).det := by
    intro z
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP0 : P ≠ 0 := by
    intro h0
    have hz := hev Complex.I
    rw [h0, Polynomial.eval_zero] at hz
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz.symm
    apply hv
    apply vec_zero g (-Complex.I) (by simp) v
    have hm : (-Complex.I) • C + D = (-Complex.I) • (C + Complex.I • D) := by
      rw [smul_add, smul_smul]
      simp
    rw [hm, Matrix.vecMul_smul, hv0, smul_zero]
  apply ((P.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot, hev]
  exact hs

theorem dense_cell : Dense {g : GR n | ((mR g).toBlocks₂₁).det ≠ 0} := by
  intro g
  have hT : Tendsto (fun s : ℝ => g * nbE s) (𝓝[≠] 0) (𝓝 g) := by
    have hc : Continuous fun s : ℝ => g * nbE s := continuous_const.mul cont_nbE
    have h := hc.tendsto 0
    rw [nbE_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hfin := finite_bad g
  have hZ : IsClosed ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  have h0 : (0 : ℝ) ∉ ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) := by simp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hZ.isOpen_compl.mem_nhds h0), self_mem_nhdsWithin] with s hs hs0
  show ((mR (g * nbE s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_mul_lowering]
  intro hdet
  exact hs ⟨hdet, hs0⟩

theorem bigcell (g : GR n) (hγ : ((mR g).toBlocks₂₁).det ≠ 0) :
    ∃ (y h : GR n) (b : Matrix (Fin n) (Fin n) ℂ), (mR y).toBlocks₂₁ = 0 ∧ b.IsHermitian ∧ mR h = JJ n * nU b ∧
      g = y * h := by
  set C := (mR g).toBlocks₂₁ with hC
  set D := (mR g).toBlocks₂₂ with hD
  have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hγ
  have huH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hγ)
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * Cᴴ⁻¹ = C⁻¹ * (C * Dᴴ) * Cᴴ⁻¹ := by rw [nonsing_inv_mul_cancel_left C _ hu]
      _ = C⁻¹ * (D * Cᴴ) * Cᴴ⁻¹ := by rw [hC, hD, lagr g]
      _ = C⁻¹ * D := by rw [← Matrix.mul_assoc, mul_nonsing_inv_cancel_right Cᴴ _ huH]
  refine ⟨g * (jjE * nuE (C⁻¹ * D) hb)⁻¹, jjE * nuE (C⁻¹ * D) hb, C⁻¹ * D, ?_, hb, ?_, by group⟩
  · have hinv : mR (jjE * nuE (C⁻¹ * D) hb)⁻¹ = nU (-(C⁻¹ * D)) * (-JJ n) := by
      rw [_root_.mul_inv_rev, mR_mul]
      rfl
    rw [mR_mul, hinv]
    conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
    simp [nU, JJ, fromBlocks_multiply, fromBlocks_neg, ← hC, ← hD]
    rw [mul_nonsing_inv_cancel_left C D hu, neg_add_cancel]
  · rw [mR_mul]
    rfl

end PositivityTheory.Rg.Sw.Glob.Vac
