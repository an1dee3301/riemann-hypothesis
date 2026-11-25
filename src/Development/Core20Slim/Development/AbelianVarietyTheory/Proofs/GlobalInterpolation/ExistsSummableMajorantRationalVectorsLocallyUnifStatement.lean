module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  first | exact @GlobalTheory.SumMaj.summable_majorant | exact GlobalTheory.SumMaj.summable_majorant | (intros; apply GlobalTheory.SumMaj.summable_majorant <;> assumption)
