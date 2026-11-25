module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Ac (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def holomorphicSectionExtension (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (h : GR n) (z : ℂ) : ℂ :=
  (mR h).det ^ e * (u1 (mR h * Ac X z)).det ^ (-(p : ℤ)) * (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))

def HelpA : Prop :=
  (∀ (n : ℕ) (X : Fin n → ℝ), ∃ a : ℝ → GR n, ∀ s, IsDil X s (a s)) ∧
  (∀ (n : ℕ) (X : Fin n → ℝ) (s : ℝ) (a a' : GR n), IsDil X s a → IsDil X s a' → a = a') ∧
  (∀ n : ℕ, IsCompact (univ : Set (KR n))) ∧
  (∀ (n : ℕ) (h : GR n), (u1 (mR h)).det ≠ 0 ∧ (u2 (mR h)).det ≠ 0) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) → ∀ (h : GR n) (s : ℝ),
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s)) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)), IsCompact S → ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
    ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧ ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V) ∧
  (∀ (n p q : ℕ) (e : ℤ), Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, k ∈ KR n → F0 p q e k ≠ 0)

def HelpC : Prop :=
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    ∀ (r : ℕ) (s : ℝ), iteratedDeriv r (fun t : ℝ => f t) s = iteratedDeriv r f s) ∧
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    (∀ r : ℕ, iteratedDeriv r f 0 = 0) → ∀ s : ℝ, f s = 0)

end PositivityTheory.Rg.Sw.AbsSt
