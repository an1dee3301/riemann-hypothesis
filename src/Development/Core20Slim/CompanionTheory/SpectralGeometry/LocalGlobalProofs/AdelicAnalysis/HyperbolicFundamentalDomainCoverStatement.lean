module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFundamentalDomainCover
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Order.Real

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_fundamental_domain_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∃ (Y : Set ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))) (Kc : ℝ≥0∞), IsCompact Y ∧ Kc < ⊤ ∧ (∀ p ∈ Y, hR (AF F) σ (hypJ J) (p.2 0) (p.1 0) = 1) ∧ ∀ Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → (∀ (l : E) y, l ≠ 0 → Φ ((inclR (F := F) (AF F) l : AF F ⊗[F] E) • y) = Φ y) → ∀ g : ℤ → ℝ≥0∞, (∀ (j : ℤ), ∀ p ∈ Y, Φ (((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1) ≤ g j) → ∀ L : Set (Fin 1 → Fin (M + 2) → E), L ⊆ {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} → (∀ X ∈ L, ∀ X' ∈ L, ∀ l : E, X' = l • X → X' = X) → cntI σ _ μ 𝓕 L Φ ≤ Kc * ∑' j : ℤ, g j * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ)))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | exact GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | (intros; apply GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum <;> assumption)
