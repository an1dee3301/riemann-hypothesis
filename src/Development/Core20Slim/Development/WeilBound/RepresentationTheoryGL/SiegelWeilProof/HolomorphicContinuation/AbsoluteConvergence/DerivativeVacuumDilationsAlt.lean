module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def KR (n : ℕ) : Subgroup (GR n) where
  carrier := {k | InK (mR k)}
  one_mem' := by
    refine ⟨(GR n).one_mem, ?_⟩
    simp [mR]
  mul_mem' := by
    intro a b ha hb
    refine ⟨(a * b).2, ?_⟩
    simp only [mR, Subgroup.coe_mul, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc b.1.1ᴴ * a.1.1ᴴ * (a.1.1 * b.1.1) = b.1.1ᴴ * (a.1.1ᴴ * a.1.1) * b.1.1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha.2, Matrix.mul_one, hb.2]
  inv_mem' := by
    intro a ha
    refine ⟨(a⁻¹).2, ?_⟩
    have h1 : a.1.1 * (a⁻¹).1.1 = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
    have ha2 : a.1.1ᴴ * a.1.1 = 1 := ha.2
    have h2 : (a⁻¹).1.1 = a.1.1ᴴ := by
      calc (a⁻¹).1.1 = (a.1.1ᴴ * a.1.1) * (a⁻¹).1.1 := by rw [ha2, Matrix.one_mul]
        _ = a.1.1ᴴ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    simp only [mR]
    rw [h2, Matrix.conjTranspose_conjTranspose]
    calc a.1.1 * a.1.1ᴴ = a.1.1 * (a⁻¹).1.1 := by rw [h2]
      _ = 1 := h1

def IsUp (p : GR n) : Prop := (mR p).toBlocks₂₁ = 0

def Iwa : Prop := ∀ (n : ℕ) (y : GR n), ∃ p k : GR n, IsUp p ∧ k ∈ KR n ∧ y = p * k

def CayleyBlocksInvertible : Prop := ∀ (n : ℕ) (y : GR n), (u1 (mR y)).det ≠ 0 ∧ (u2 (mR y)).det ≠ 0

def KAK : Prop := ∀ (n : ℕ) (y : GR n), ∃ (k₁ k₂ a : GR n) (X : Fin n → ℝ), k₁ ∈ KR n ∧ k₂ ∈ KR n ∧ IsDil X 1 a ∧ y = k₁ * a * k₂

def Mult : Prop := ∀ (n p q : ℕ) (e : ℤ),
  (∀ (g : GR n) (k : GR n), k ∈ KR n → F0 p q e (g * k) = F0 p q e g * F0 p q e k ∧ hLoc (g * k) = hLoc g) ∧
  ∀ (y g : GR n), IsUp y → F0 p q e (y * g) = F0 p q e y * F0 p q e g ∧ hLoc (y * g) = hLoc y * hLoc g

def SecZero : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ P, NullSec ε c P ↔ ∀ y, sL P y = 0

def DerivativeVacuumDilations : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    ∀ (y : GR n) (r : ℕ), HasDerivAt (fun s : ℝ => iteratedDeriv r (fun s' : ℝ => F0 p q e (y * a s')) s)
      (sL ((dil c X ^ (r + 1)) 1) y) 0 ∧ iteratedDeriv r (fun s : ℝ => F0 p q e (y * a s)) 0 = sL ((dil c X ^ r) 1) y

def CycSec : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ L : C(KR n, ℂ) →L[ℂ] ℂ, (∀ y : GR n, ∀ h : C(KR n, ℂ), (∀ k, h k = F0 p q e ((k : GR n) * y)) → L h = 0) →
      ∀ P (h : C(KR n, ℂ)), (∀ k, h k = sL P (k : GR n)) → L h = 0

def Sph : Prop := ∀ (n p q : ℕ) (e : ℤ) [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure]
  [IsProbabilityMeasure μ] (y z : GR n),
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (y * (k : GR n) * z) ∂μ =
    F0 p q e y * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * z) ∂μ

def LocOp : Prop := ∀ (n p q : ℕ) (e : ℤ), GoodSig n p q → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n))
  [μ.IsHaarMeasure] [IsProbabilityMeasure μ],
  ∃ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : GR n) (nb : (Fin n → Fin n → ℝ) → GR n) (cz : ℂ → ℂ),
    IsSingTest ψ ∧ (∀ x, mR (nb x) = nU (herm x)) ∧ Continuous nb ∧ Differentiable ℂ cz ∧ cz 0 ≠ 0 ∧
    ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y)

def HolParam : Prop := ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [IsFiniteMeasure μ] (C : Set X), IsCompact C → μ Cᶜ = 0 → ∀ (U : Set ℂ) (F : X → ℂ → ℂ), IsOpen U →
    ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U) → (∀ x ∈ C, DifferentiableOn ℂ (F x) U) →
    DifferentiableOn ℂ (fun z => ∫ x, F x z ∂μ) U ∧
      ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ x, F x z ∂μ) z = ∫ x, iteratedDeriv r (F x) z ∂μ


def Glue : Prop := ∀ (U : Set ℂ) (f h : ℂ → ℂ) (σ : ℝ) (s₀ : ℂ), IsOpen U → GlobalTheory.Cont.IsRightDomain U → s₀ ∈ U →
  MeromorphicOn f U → AnalyticAt ℂ f s₀ → GlobalTheory.Cont.rightOf σ ⊆ U → DifferentiableOn ℂ h (GlobalTheory.Cont.rightOf σ) →
  (∀ z ∈ GlobalTheory.Cont.rightOf σ, ∀ᶠ w in 𝓝[≠] z, f w = h w) → GlobalTheory.Cont.HolValueAt h s₀ (f s₀)

end PositivityTheory.Rg.Sw.AbsSt
