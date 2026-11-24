module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDef
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect : ∀ (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)), Continuous c → c 0 ≠ 0 → IsOpen U → (∀ s, (s, 0) ∈ U) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U → (∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  first | exact @GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | exact GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | (intros; apply GlobalTheory.FuncEqSmooth.contDiff_of_func_eq <;> assumption)
