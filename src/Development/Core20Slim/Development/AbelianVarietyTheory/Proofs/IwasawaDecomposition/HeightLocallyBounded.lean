module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftHeight

theorem height_locally_bounded : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ g₀ : GA D V,
    ∃ C : ℝ, ∀ᶠ g in 𝓝 g₀, (height θ V g : ℝ) ≤ C := by
  intro D θ hθ V g₀
  obtain ⟨C, hC, h⟩ := GlobalTheory.Grow.height_comparison V hθ
  have hc := (GlobalTheory.Grow.continuous_height V).continuousAt (x := g₀)
  refine ⟨C * (GlobalTheory.Grow.height V g₀ + 1), ?_⟩
  filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one _)] with g hg
  exact (h g).1.trans (mul_le_mul_of_nonneg_left hg.le hC.le)

end GlobalTheory.Mem.LiftHeight

end
