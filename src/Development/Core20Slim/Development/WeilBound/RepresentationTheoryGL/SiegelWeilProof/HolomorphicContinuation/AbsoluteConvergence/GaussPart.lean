module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def bS (X : Fin n → ℝ) (h : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) * b * diagonal (fun j => (Real.exp (-(h * X j)) : ℂ))

def GaussPart : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (X : Fin n → ℝ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    ∀ Q : PX m n, HasDerivAt (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b))
      (secN ε c t (dil c X Q) b) 0

def GroupPart : Prop :=
  ∀ (n : ℕ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    (∀ s s', a (s + s') = a s * a s') ∧ a 0 = 1 ∧ (∀ s, IsUp (a s)) ∧ Continuous a ∧
    (∀ y : GR n, IsUp y → ∀ s, IsUp (y * a s)) ∧
    (∀ (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∃ (y₁ g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
      mR g = JJ n * nU b ∧ y = y₁ * g) ∧
    (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), mR g = JJ n * nU b → ∀ h, mR (a h * g * a h) = JJ n * nU (bS X h b)) ∧
    (∀ y : GR n, (mR y).toBlocks₂₁.det ≠ 0 → ∀ s, (mR (y * a s)).toBlocks₂₁.det ≠ 0) ∧
    Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ∧
    ∀ (p q : ℕ) (e : ℤ) (h : ℝ), F0 p q e (a (-h)) = Complex.exp (-((h * ((p + q : ℕ) * ∑ j, X j) : ℝ) : ℂ))

end PositivityTheory.Rg.Sw.AbsSt.DF
