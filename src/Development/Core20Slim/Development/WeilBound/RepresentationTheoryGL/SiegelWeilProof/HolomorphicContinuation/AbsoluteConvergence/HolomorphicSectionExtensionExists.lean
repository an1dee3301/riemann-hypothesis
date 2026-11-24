module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalSectionContinuousNeZero
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Prod
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem mR_dil (X : Fin n → ℝ) (s : ℝ) (a : GR n) (h : IsDil X s a) : mR a = Ac X s := by
  rw [h]
  unfold Ac
  congr 2 <;> funext j <;> push_cast [Complex.ofReal_exp] <;> (try ring_nf)

theorem det_Ac (X : Fin n → ℝ) (z : ℂ) : (Ac X z).det = 1 := by
  unfold Ac
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add]
  try simp

theorem holomorphic_section_extension_eq (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n) (ha : ∀ s, IsDil X s (a s)) (h : GR n) (s : ℝ) :
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s) := by
  unfold holomorphicSectionExtension F0 f0
  rw [mR_mul, mR_dil X s (a s) (ha s), det_mul, det_Ac, mul_one, mul_assoc]

theorem continuous_Ac (X : Fin n → ℝ) : Continuous (Ac X) := by
  unfold Ac
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const ?_
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)

theorem differentiable_Ac_entry (X : Fin n → ℝ) (a b : Fin n ⊕ Fin n) : Differentiable ℂ fun z => Ac X z a b := by
  rcases a with a | a <;> rcases b with b | b <;> by_cases hab : a = b <;>
    simp [Ac, diagonal_apply, hab] <;> fun_prop

theorem differentiable_det_entries {m : Type} [Fintype m] [DecidableEq m] (A : ℂ → Matrix m m ℂ)
    (hA : ∀ i j, Differentiable ℂ fun z => A z i j) : Differentiable ℂ fun z => (A z).det := by
  have : (fun z => (A z).det) = fun z => ∑ σ : Equiv.Perm m, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i := by
    funext z
    rw [det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [this]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (differentiable_const _).mul (Differentiable.fun_finsetProd fun i _ => hA _ _)

theorem differentiable_u_det (M : M2 n) (X : Fin n → ℝ) (w : ℂ) :
    Differentiable ℂ fun z => (w • (M * Ac X z).toBlocks₂₁ + (M * Ac X z).toBlocks₂₂).det := by
  apply differentiable_det_entries
  intro i j
  have hm : ∀ a b, Differentiable ℂ fun z => (M * Ac X z) a b := by
    intro a b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (differentiable_Ac_entry X k b)
  simp only [Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, of_apply, smul_eq_mul]
  exact ((differentiable_const _).mul (hm _ _)).add (hm _ _)

theorem continuous_u_det (X : Fin n → ℝ) (w : ℂ) :
    Continuous fun y : GR n × ℂ => (w • (mR y.1 * Ac X y.2).toBlocks₂₁ + (mR y.1 * Ac X y.2).toBlocks₂₂).det := by
  have hM : Continuous fun y : GR n × ℂ => mR y.1 * Ac X y.2 :=
    (continuous_mR.comp continuous_fst).matrix_mul ((continuous_Ac X).comp continuous_snd)
  have h21 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₁ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))
  have h22 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₂ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))
  exact ((h21.const_smul w).add h22).matrix_det

theorem first_cayley_block_eq (M : M2 n) : u1 M = Complex.I • M.toBlocks₂₁ + M.toBlocks₂₂ := rfl

theorem second_cayley_block_eq (M : M2 n) : u2 M = (-Complex.I) • M.toBlocks₂₁ + M.toBlocks₂₂ := by
  simp [u2, neg_smul]

theorem holomorphic_section_extension_exists (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)) (hS : IsCompact S) :
    ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
      ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧
      ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V := by
  have c1 : Continuous fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det := by
    simpa only [first_cayley_block_eq] using continuous_u_det X Complex.I
  have c2 : Continuous fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det := by
    simpa only [second_cayley_block_eq] using continuous_u_det X (-Complex.I)
  set Z := {y : GR n × ℂ | (u1 (mR y.1 * Ac X y.2)).det ≠ 0 ∧ (u2 (mR y.1 * Ac X y.2)).det ≠ 0}
  have hZ : IsOpen Z := (isOpen_ne_fun c1 continuous_const).inter (isOpen_ne_fun c2 continuous_const)
  have hreal : ∀ (h : GR n) (s : ℝ), ((h, (s : ℂ)) : GR n × ℂ) ∈ Z := by
    intro h s
    have hm : mR h * Ac X s = mR (h * aD X s) := by rw [mR_mul, mR_dil X s _ (isDil_aD X s)]
    refine ⟨?_, ?_⟩
    · show (u1 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_first_det_ne_zero _
    · show (u2 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_second_det_ne_zero _
  have tube : ∀ s : ℝ, ∃ v : Set ℂ, IsOpen v ∧ (s : ℂ) ∈ v ∧ S ×ˢ v ⊆ Z := by
    intro s
    obtain ⟨u, v, -, hv, hSu, hsv, huv⟩ := generalized_tube_lemma hS (isCompact_singleton (x := (s : ℂ))) hZ
      (by
        rintro ⟨h, z⟩ ⟨-, hz⟩
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hreal h s)
    exact ⟨v, hv, hsv rfl, (Set.prod_mono hSu le_rfl).trans huv⟩
  choose v hv hsv hSv using tube
  refine ⟨⋃ s, v s, isOpen_iUnion hv, fun s => Set.mem_iUnion.mpr ⟨s, hsv s⟩, ?_, ?_⟩
  · have hsub : S ×ˢ (⋃ s, v s) ⊆ Z := by
      rintro ⟨h, z⟩ ⟨hh, hz⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
      exact hSv s (Set.mk_mem_prod hh hs)
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    have hyZ := hsub hy
    unfold holomorphicSectionExtension
    have e1 : ContinuousAt (fun y : GR n × ℂ => (mR y.1).det ^ e) y :=
      ((continuous_mR.comp continuous_fst).matrix_det.continuousAt).zpow₀ _ (Or.inl (det_mR_ne _))
    have e2 : ContinuousAt (fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det ^ (-(p : ℤ))) y :=
      c1.continuousAt.zpow₀ _ (Or.inl hyZ.1)
    have e3 : ContinuousAt (fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det ^ (-(q : ℤ))) y :=
      c2.continuousAt.zpow₀ _ (Or.inl hyZ.2)
    exact (e1.mul e2).mul e3
  · intro h hh z hz
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
    have hyZ := hSv s (Set.mk_mem_prod hh hs)
    have d1 : Differentiable ℂ fun z => (u1 (mR h * Ac X z)).det := by
      simpa only [first_cayley_block_eq] using differentiable_u_det (mR h) X Complex.I
    have d2 : Differentiable ℂ fun z => (u2 (mR h * Ac X z)).det := by
      simpa only [second_cayley_block_eq] using differentiable_u_det (mR h) X (-Complex.I)
    unfold holomorphicSectionExtension
    have g1 : DifferentiableAt ℂ (fun z => (u1 (mR h * Ac X z)).det ^ (-(p : ℤ))) z := (d1 z).zpow (Or.inl hyZ.1)
    have g2 : DifferentiableAt ℂ (fun z => (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))) z := (d2 z).zpow (Or.inl hyZ.2)
    exact (((differentiableAt_const _).mul g1).mul g2).differentiableWithinAt

end PositivityTheory.Rg.Sw.AbsSt
