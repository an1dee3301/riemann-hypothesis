module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursion
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_bound_by_recursion : ∀ (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞), Dtot ≠ ⊤ → (∀ Y, MeasurableSet Y → D Y ≤ Dtot) → ∀ (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0), (∀ Y, MeasurableSet Y → ∃ Z : ι → Set H, (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧ D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i)) → ∑ i ∈ I, α i * β i < 1 → ∑ i ∈ I, α i < 1 → ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | exact GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | (intros; apply GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated <;> assumption)
