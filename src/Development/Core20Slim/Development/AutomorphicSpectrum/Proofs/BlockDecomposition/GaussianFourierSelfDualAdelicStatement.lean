module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianFourierSelfDualAdelic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_fourier_self_dual_adelic : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a 0 * Dinf (fun _ => 0)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core0.core_zero | exact GlobalTheory.CompanionTheory.SW.Core0.core_zero | (intros; apply GlobalTheory.CompanionTheory.SW.Core0.core_zero <;> assumption)
