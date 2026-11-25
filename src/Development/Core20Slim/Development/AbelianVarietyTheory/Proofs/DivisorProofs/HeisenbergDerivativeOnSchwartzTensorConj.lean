module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem heisenbergDeriv_tensor_conj (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) := by
  let L₁ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inl i))
  let L₂ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inr i))
  have hL₁ : ∀ y, L₁ y = y ∘ Sum.inl := fun y => rfl
  have hL₂ : ∀ y, L₂ y = y ∘ Sum.inr := fun y => rfl
  have hfun : (f₀ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ) = fun y => f (L₁ y) * Complex.conjCLE (f (L₂ y)) := by
    funext y; rw [hf₀]; rfl
  have hd₁ : HasFDerivAt (fun y => f (L₁ y)) ((fderiv ℝ f (L₁ x)).comp L₁) x :=
    (f.differentiableAt.hasFDerivAt).comp x L₁.hasFDerivAt
  have hd₂ : HasFDerivAt (fun y => Complex.conjCLE (f (L₂ y)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x ((f.differentiableAt.hasFDerivAt).comp x L₂.hasFDerivAt)
  have hD : fderiv ℝ f₀ x = f (L₁ x) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) + Complex.conjCLE (f (L₂ x)) • ((fderiv ℝ f (L₁ x)).comp L₁) := by
    rw [hfun]
    exact (hd₁.mul hd₂).fderiv
  have hevneg : ∀ b : AF F, evI F (-b) = - evI F b := by
    intro b
    unfold evI
    rw [show (-b).1 = -b.1 from rfl, map_neg]
  have htr : (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ)
      = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inl) i * evI F (b₁ i))
        - Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inr) i * evI F (b₂ i)) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hevneg, mul_neg, Finset.sum_neg_distrib,
      map_add, map_neg, Function.comp_apply]
    ring
  rw [hh x, hg₁, hg₂, hD, htr, hf₀]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, hL₁, hL₂, smul_eq_mul]
  have e1 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inl) = fun i => evI F (a₁ i) := rfl
  have e2 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inr) = fun i => evI F (a₂ i) := rfl
  rw [e1, e2]
  simp only [star_sub, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

end GlobalTheory
