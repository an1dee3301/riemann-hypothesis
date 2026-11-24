module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartz
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_bound_periodic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ, Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) → ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  first | exact @GlobalTheory.ArchDecay.sobolev_per | exact GlobalTheory.ArchDecay.sobolev_per | (intros; apply GlobalTheory.ArchDecay.sobolev_per <;> assumption)
