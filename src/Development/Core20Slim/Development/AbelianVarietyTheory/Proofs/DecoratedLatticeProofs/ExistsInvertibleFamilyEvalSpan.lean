module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

def evalLin {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, MvPolynomial.smul_eval]

theorem evalLin_apply {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalLin y F = evalAt y F := rfl

theorem exists_evalAt_span (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ)
    (W : Type) [AddCommGroup W] [Module ℂ W] (T : PY ι a →ₗ[ℂ] W) :
    ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → W),
      (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, T F = ∑ j, evalAt (y j) F • P j := by
  classical
  set V := Vn lam n with hV
  haveI : FiniteDimensional ℂ V := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).1
  have hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0 :=
    (GlobalTheory.T.fockSubstitution_identities ι a a le_rfl).2.2.2.2.2.2.1
  let S : Set (Module.Dual ℂ V) :=
    {φ | ∃ y : ι → Matrix (Fin a) (Fin a) ℂ, IsInv y ∧ φ = (evalLin y).comp V.subtype}
  obtain ⟨f, hfS, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ S
  choose y hy hfy using hfS
  let Φ := LinearMap.pi f
  have hinj : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro F hF
    have h0 : ∀ φ ∈ Submodule.span ℂ S, φ F = 0 := by
      intro φ hφ
      rw [← hspan] at hφ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact congrFun hF j
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]
    have hF0 : (F : PY ι a) = 0 := by
      apply hsep
      intro z hz
      have := h0 ((evalLin z).comp V.subtype) (Submodule.subset_span ⟨z, hz, rfl⟩)
      simpa [evalLin_apply] using this
    exact Subtype.ext hF0
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Φ hinj
  refine ⟨_, y, fun j => T (L (Pi.single j 1) : PY ι a), hy, ?_⟩
  intro F hF
  have hΦ : Φ ⟨F, hF⟩ = ∑ j, evalAt (y j) F • (Pi.single j 1 : Fin _ → ℂ) := by
    ext i
    simp only [Φ, LinearMap.pi_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hfy i]
    rfl
  have key : (⟨F, hF⟩ : V) = L (Φ ⟨F, hF⟩) := by
    rw [← LinearMap.comp_apply, hL]; rfl
  calc T F = T ((⟨F, hF⟩ : V) : PY ι a) := rfl
    _ = T ((L (Φ ⟨F, hF⟩) : V) : PY ι a) := by rw [← key]
    _ = ∑ j, evalAt (y j) F • T (L (Pi.single j 1) : PY ι a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΦ, map_sum]
      simp [map_smul, Submodule.coe_sum, Submodule.coe_smul]

end GlobalTheory.KJInf
