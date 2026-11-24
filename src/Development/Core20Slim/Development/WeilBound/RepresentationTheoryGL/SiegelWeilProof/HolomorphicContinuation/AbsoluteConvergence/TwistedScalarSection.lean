module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOp
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
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
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

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def aZ {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def twistedScalarSection {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) : ℂ := M.det ^ e * f0 p q M

def TSBFacts : Prop :=
  CayleyBlocksInvertible → ∀ (n p q : ℕ) (e : ℤ),
    CompactSpace (KR n) ∧ Continuous (mR : GR n → M2 n) ∧ Continuous (F0 p q e : GR n → ℂ) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ), ∃ a : GR n, IsDil X t a) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ) (a : GR n), IsDil X t a → mR a = aZ X t) ∧
    ∀ (X : Fin n → ℝ) (C : Set (GR n)), IsCompact C → ∃ U : Set ℂ, IsOpen U ∧ (∀ t : ℝ, (t : ℂ) ∈ U) ∧
      ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U) ∧
      ∀ y ∈ C, DifferentiableOn ℂ (fun z => twistedScalarSection p q e (mR y * aZ X z)) U

end PositivityTheory.Rg.Sw.AbsSt
