module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ), (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) → FiniteDimensional ℂ U := by
  first | exact @GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | exact GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | (intros; apply GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits <;> assumption)
