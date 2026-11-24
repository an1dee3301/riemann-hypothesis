module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImage
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  first | exact @GlobalTheory.RowFubini.haar_trace_conj_eq | exact GlobalTheory.RowFubini.haar_trace_conj_eq | (intros; apply GlobalTheory.RowFubini.haar_trace_conj_eq <;> assumption)
