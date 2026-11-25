module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Norm.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_measure_scaling : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → (∀ (c : F), c ≠ 0 → ∀ s : Set (A F), MeasurableSet s → lf ((fun x => algebraMap F (A F) c * x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹) * lf s) ∧ (∀ b : F, lf {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} = ((den b : ℝ≥0∞))⁻¹) ∧ ∀ (a : (A F)ˣ) (s : Set (A F)), MeasurableSet s → lf ((fun x => (a : A F) * x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) * lf s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | exact GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale <;> assumption)
