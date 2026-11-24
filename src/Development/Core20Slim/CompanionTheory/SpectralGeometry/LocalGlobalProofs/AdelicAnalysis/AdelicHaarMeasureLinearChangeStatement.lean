module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Norm.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_measure_linear_change : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | exact GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale <;> assumption)
