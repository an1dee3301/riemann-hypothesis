module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralFinitelyManyCellsWeightedSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientIntegral_finitelyManyCells_weightedSum : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G), IsClosed (R : Set G) → IsCompact (K : Set G) → IsOpen (K : Set G) → ∀ (ρ : Measure R) (μ : Measure G), ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → μ.IsMulRightInvariant → ∀ T : Finset G, ∃ (T' : Finset G) (w : G → ℂ), T' ⊆ T ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ g, f g ≠ 0 → ∃ q ∈ T, ∃ r ∈ R, ∃ k ∈ K, g = r * q * k) → IsQuotIntL1 ρ μ f (∑ q ∈ T', w q * f q) := by
  first | exact @GlobalTheory.CellInt.quotInt_finiteCells | exact GlobalTheory.CellInt.quotInt_finiteCells | (intros; apply GlobalTheory.CellInt.quotInt_finiteCells <;> assumption)
