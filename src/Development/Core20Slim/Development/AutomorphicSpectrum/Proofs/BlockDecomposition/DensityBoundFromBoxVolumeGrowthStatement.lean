module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundFromBoxVolumeGrowth
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Notation

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_bound_from_box_volume_growth : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ), 0 < n → 2 * n < M → ∀ (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → (∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q S C → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s '' S) C) → ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) \ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK κ R ε) δ := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density <;> assumption)
