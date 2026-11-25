module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParam
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Init.Core
public import Init.Data.Zero
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
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam : ∀ (l : Type) [Fintype l] [DecidableEq l] (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ), Continuous g → g 0 = 1 →
    (∀ s t, g (s + t) = g s * g t) → (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ t : ℝ, g t = NormedSpace.exp (t • Z) := by
  first | exact @GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp | exact GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp | (intros; apply GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp <;> assumption)
