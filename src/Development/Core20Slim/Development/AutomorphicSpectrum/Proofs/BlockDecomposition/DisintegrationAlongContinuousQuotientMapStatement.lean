module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationAlongContinuousQuotientMap
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disintegration_along_continuous_quotient_map : ∀ (V H Z : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H] (μ : Measure V) (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (f : V → Z) (ι : H → Z) (q : V → H) (U : Set V) (m : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ X, ι (q X) = f X) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ m → ∀ φ : V → ℂ, Continuous φ → Integrable φ μ → (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ A : Set V, IsCompact A ∧ A ⊆ U ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y) → ∀ c : H, Integrable φ (m c) ∧ ∀ r : ℕ → H → ℝ, (∀ k, Continuous (r k) ∧ HasCompactSupport (r k) ∧ (∀ y, 0 ≤ r k y) ∧ 0 < ∫ y, r k y ∂ν) → Filter.Tendsto (fun k => tsupport (r k)) Filter.atTop (nhds c).smallSets → Filter.Tendsto (fun k => (∫ X, φ X * (r k (q X) : ℂ) ∂μ) / ((∫ y, r k y ∂ν : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(m c))) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto <;> assumption)
