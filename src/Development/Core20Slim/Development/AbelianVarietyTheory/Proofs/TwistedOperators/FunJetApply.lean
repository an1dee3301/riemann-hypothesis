module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.StatementA
public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.RealPlaceAnalysis.StatementU
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix Formalism.REAL Filter Topology
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

variable {n : ℕ}

def actM {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (Z : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ V :=
  ∑ a, ∑ b, Z a b • E a b

def thE (ε : Fin n → Bool) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  -((sgn ε p.1 p.2 : ℝ) : ℂ) • Matrix.single p.2 p.1 (1 : ℂ)

def thM (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p : Fin n × Fin n, Z p.1 p.2 • thE ε p

def arr1 {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (j : W →ₗᵢ[ℂ] V) (G : Fin n × Fin n → W) : Arr V n 1 :=
  arrTo V n 1 fun α => j (G (α 0))

def Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  fun z => fderiv ℂ f z (z * Z)

def Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool) (l : List (Fin n × Fin n))
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  l.foldr (fun p g => Rz (thE ε p) g) f

def formOf {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : W →ₗ[ℂ] W) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ).compl₂ T

def funJet {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  formOf (Rw ε l f 1 : W →L[ℂ] W).toLinearMap

theorem funJet_apply {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) (y x : W) :
    funJet ε f l y x = ⟪y, Rw ε l f 1 x⟫_ℂ := rfl

def modJet {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n)) :
    W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  ((innerₛₗ ℂ).compl₂ (ew E l ∘ₗ j.toLinearMap)) ∘ₛₗ j.toLinearMap

theorem modJet_apply {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n))
    (y x : W) : modJet E j l y x = ⟪j y, ew E l (j x)⟫_ℂ := rfl

section Rel

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W]

def JetRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n),
    B (l₁ ++ (a, b) :: (c, d) :: l₂) - B (l₁ ++ (c, d) :: (a, b) :: l₂) =
      (if b = c then B (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then B (l₁ ++ (c, b) :: l₂) else 0)) ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y x x' : W, j x' = E a b (j x) →
    B (l ++ [(a, b)]) y x = B l y x') ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y y' x : W, j y' = E b a (j y) →
    B ((a, b) :: l) y x = B l y' x) ∧
  ∀ (l : List (Fin n × Fin n)) (G : Fin n × Fin n → W), arr1 j G ∈ Vminus ε E Λ u →
    ∀ y : W, ∑ p, B (l ++ [p]) y (G p) = 0

theorem JetRel.sub {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V}
    {j : W →ₗᵢ[ℂ] V} {B B' : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (h : JetRel ε E Λ u j B)
    (h' : JetRel ε E Λ u j B') : JetRel ε E Λ u j (fun l => B l - B' l) := by
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b hab y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have h1 := h.1 l₁ l₂ a b c d
    have h2 := h'.1 l₁ l₂ a b c d
    rw [sub_sub_sub_comm, h1, h2]
    split_ifs <;> (ext y x; simp only [LinearMap.sub_apply, LinearMap.zero_apply]; ring)
  · simp only [LinearMap.sub_apply, h.2.1 l a b hab y x x' hx, h'.2.1 l a b hab y x x' hx]
  · simp only [LinearMap.sub_apply, h.2.2.1 l a b hab y y' x hy, h'.2.2.1 l a b hab y y' x hy]
  · simp only [LinearMap.sub_apply, Finset.sum_sub_distrib, h.2.2.2 l G hG y, h'.2.2.2 l G hG y, sub_self]

def FunEquiv (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    (∀ x x' : W, j x' = E a b (j x) → fderiv ℂ f z (z * thE ε (a, b)) x = f z x') ∧
    ∀ y y' x : W, j y' = E b a (j y) → ⟪y, fderiv ℂ f z (thE ε (a, b) * z) x⟫_ℂ = ⟪y', f z x⟫_ℂ

def FunSchmid (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    ∑ p, fderiv ℂ f z (z * thE ε p) (G p) = 0

def TauTie (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ Y, inK ε Y → ∀ v v' : W, j v' = actM E (Y.map star) (j v) →
    HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y)) v) v' 0

def LowData (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) :
    Prop :=
  GlRel E ∧ IsUnitary ε E ∧ KHighest ε E Λ u ∧ FiniteDimensional ℂ (kSpan ε E u) ∧
    LinearMap.range j.toLinearMap = kSpan ε E u

def DerTie {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) : Prop :=
  ∀ X, inG ε X → ∀ v : V,
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (ι v)) (ι (actM E X v)) 0

end Rel

end GlobalTheory.SphJet
