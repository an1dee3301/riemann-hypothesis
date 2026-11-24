module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (N : ℕ), ∃ N' : ℕ, ∀ K : GA D V → GA D W → ℂ, (∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h) → (∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧ IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h) → (∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W, ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N) → ∃ C : ℝ, ∀ g h, ‖K g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N' := by
  first | exact @GlobalTheory.Mem.LiftGrow.growth_pair | exact GlobalTheory.Mem.LiftGrow.growth_pair | (intros; apply GlobalTheory.Mem.LiftGrow.growth_pair <;> assumption)
