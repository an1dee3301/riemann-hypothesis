module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBounds
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds : ∀ {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) → (∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  first | exact @GlobalTheory.contDiff_tsum_of_locally_summable_bounds | exact GlobalTheory.contDiff_tsum_of_locally_summable_bounds | (intros; apply GlobalTheory.contDiff_tsum_of_locally_summable_bounds <;> assumption)
