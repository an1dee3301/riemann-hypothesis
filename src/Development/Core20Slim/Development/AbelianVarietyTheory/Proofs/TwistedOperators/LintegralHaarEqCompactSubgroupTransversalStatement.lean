module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversal
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal : ∀ (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G), Measurable e → mK Kᶜ = 0 → (∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) → lam ≠ 0 → (∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤) → (∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧ ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) → ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f → ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  first | exact @GlobalTheory.Twist.lintegral_haar_eq_transversal | exact GlobalTheory.Twist.lintegral_haar_eq_transversal | (intros; apply GlobalTheory.Twist.lintegral_haar_eq_transversal <;> assumption)
