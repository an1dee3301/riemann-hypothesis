module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecay
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_of_lattice_decay_of_injective : ∀ (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ), Function.Injective f → ∀ (N : ℕ), 0 < N → ∀ (C : ℝ), (∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C) → (∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) → Summable w := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | exact GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | (intros; apply GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay <;> assumption)
