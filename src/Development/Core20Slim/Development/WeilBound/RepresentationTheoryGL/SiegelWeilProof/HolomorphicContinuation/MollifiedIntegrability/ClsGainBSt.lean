module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Mc (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cpart (i j : Fin n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b (Matrix.single i j 1)

def word (L : List (Fin n × Fin n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun ij g => cpart ij.1 ij.2 g) F

def DeltaC (F : Mc n → ℂ) : Mc n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => cpart (σ k) k g) F

def Fr (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (b : Mc n) : ℂ :=
  (1 - (Complex.I * s) • b)⁻¹.det ^ p * (1 + (Complex.I * s) • b)⁻¹.det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) R

def Ugood (s : ℂ) : Set (Mc n) := {b | IsUnit (1 - (Complex.I * s) • b).det ∧ IsUnit (1 + (Complex.I * s) • b).det}

def pdisc (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ) : Set (Mc n) := {b | ∀ i j, ‖b i j - b₀ i j‖ ≤ ρ i j}

def CauchyW : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ), (∀ i j, 0 < ρ i j) → pdisc b₀ ρ ⊆ U →
    ∀ M : ℝ, (∀ b ∈ pdisc b₀ ρ, ‖F b‖ ≤ M) → ∀ L : List (Fin n × Fin n),
      ‖word L F b₀‖ ≤ (L.map fun ij => (L.length : ℝ) / ρ ij.1 ij.2).prod * M

def Invar : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ N : ℕ, ∀ b, k * b * kᴴ ∈ U →
      (DeltaC^[N] (fun c => F (k * c * kᴴ))) b = (DeltaC^[N] F) (k * b * kᴴ)

def PBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    IsOpen (Ugood (n := n) s) ∧ ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) ∧
    ∃ (c₀ C : ℝ), 0 < c₀ ∧ ∀ (k : Mc n), k ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ (lam : Fin n → ℝ),
      ∀ b ∈ pdisc (Matrix.diagonal fun i => (lam i : ℂ)) (fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|))),
        k * b * kᴴ ∈ Ugood s ∧ ‖Fr s p q R (k * b * kᴴ)‖ ≤ C * (∏ i, (1 + |lam i|)) ^ (-((p + q : ℕ) : ℝ))

def Link : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U → (∀ y, herm y ∈ U) →
    (∀ N y, (Delta^[N] (fun y => F (herm y))) y = (DeltaC^[N] F) (herm y)) ∧
    ∀ N : ℕ, ∀ b ∈ U, (DeltaC^[N] F) b = ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F b

end PositivityTheory.Rg.Sw.WR.K.GB
