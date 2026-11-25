module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Cm (n : ℕ) : M2 n := fromBlocks (Complex.I • 1) (-(Complex.I • 1)) 1 1

def mX (P Q R S : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks P Q R S * (Cm n)⁻¹

def wM (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := (u2 x)⁻¹ * u1 x

def ub1 (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := x⁻¹.toBlocks₁₁ + Complex.I • x⁻¹.toBlocks₂₁

def fV (p q : ℤ) (x : M2 n) : ℂ := (u1 x).det ^ (p - n) * (u2 x).det ^ q * (ub1 x).det ^ (-(n : ℤ))

def blkA (j : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < j

def blkB (j : ℕ) : Finset (Fin n) := (blkA j)ᶜ

def minorOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))).det

def embOn (s : Finset (Fin n)) (T : Matrix s s ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if h : a ∈ s ∧ b ∈ s then T ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def detD {ι : Type} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℂ) *
    iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single ((Fintype.equivFin ι).symm i)
      (σ ((Fintype.equivFin ι).symm i)) 1)

def Cayley : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (t : ℤ),
    detD (fun T : Matrix ι ι ℂ => (1 + A * T).det ^ t) =
      (∏ i ∈ Finset.range (Fintype.card ι), ((t : ℂ) + i)) * A.det

def UAct : Prop :=
  ∀ (n : ℕ) (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ),
    u1 (x * mX P Q R S) = u1 x * P + u2 x * R ∧ u2 (x * mX P Q R S) = u1 x * Q + u2 x * S

def DjSec : Prop :=
  ∀ (n j : ℕ) (p q : ℤ) (x : M2 n), j ≤ n → (u1 x).det ≠ 0 → (u2 x).det ≠ 0 →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
    (∏ i ∈ Finset.range j, (-(q : ℂ) + i)) * (∏ i ∈ Finset.range (n - j), (-(p : ℂ) + i)) *
      f0 p q x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹

def DpDual : Prop :=
  ∀ (n j : ℕ) (p q : ℤ) (x : M2 n), j ≤ n → InG x →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1))) =
    (∏ i ∈ Finset.range j, ((p : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), ((q : ℂ) - n + i)) *
      fV p q x * minorOn (blkA j) (wM x)⁻¹ * minorOn (blkB j) (wM x)

def GSet (n : ℕ) : Set (M2 n) := {g | InG g}

def HolInt : Prop :=
  ∀ (n : ℕ) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] (Ω : Set (M2 n)) (F : Kg → M2 n → ℂ), IsOpen Ω →
    (∀ N : ℕ, ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (F y.1) y.2) (Set.univ ×ˢ Ω)) →
    (∀ k, ContDiffOn ℂ ∞ (F k) Ω) →
    ContDiffOn ℂ ∞ (fun x => ∫ k, F k x ∂μ) Ω ∧ ∀ (N : ℕ) (x : M2 n) (v : Fin N → M2 n), x ∈ Ω →
      iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x v = ∫ k, iteratedFDeriv ℂ N (F k) x v ∂μ

def HolZero : Prop :=
  ∀ (n : ℕ) (Ω : Set (M2 n)) (F : M2 n → ℂ), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℂ ∞ F Ω →
    (∀ g ∈ GSet n, F g = 0) → ∀ (N : ℕ) (g : M2 n), InG g → iteratedFDeriv ℂ N F g = 0

def SingToDiff : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) (r : ℝ), 0 < r → ContDiffOn ℂ ∞ G (Metric.ball 0 r) →
    (∀ ψ, IsSingTest ψ → ∫ x, G (herm x) * ψ x = 0) → detD G = 0

def TopComp : Prop :=
  ∀ (n j : ℕ) (F : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℂ ∞ F Ω →
    (∀ x P S, x * mX (1 + P) 0 0 (1 + S) ∈ Ω → x ∈ Ω → (∀ a b, P a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j) →
      (∀ a b, S a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) → F (x * mX (1 + P) 0 0 (1 + S)) = F x) →
    (∀ a b, InG a → InG b → detD (fun H => F (a * nU H * b)) = 0) →
    ∀ g, InG g → detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      F (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) = 0

def InfInv : Prop :=
  ∀ (n : ℕ) (F1 F2 : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℂ ∞ F1 Ω →
    ContDiffOn ℂ ∞ F2 Ω →
    (∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x →
      F1 (p * x) * F2 (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * (F1 x * F2 x)) →
    ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
      [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∀ Z : M2 n, ∫ k, (fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z)) ∂μ = 0

end PositivityTheory.Rg.Sw.LVs
