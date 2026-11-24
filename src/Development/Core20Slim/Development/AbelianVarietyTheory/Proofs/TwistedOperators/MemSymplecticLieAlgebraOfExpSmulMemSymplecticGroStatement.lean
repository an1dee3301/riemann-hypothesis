module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup : ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), (∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) → X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  first | exact @GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | exact GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup | (intros; apply GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup <;> assumption)
