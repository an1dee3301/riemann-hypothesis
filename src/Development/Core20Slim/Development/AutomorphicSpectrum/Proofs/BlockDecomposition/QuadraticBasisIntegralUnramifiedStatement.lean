module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralUnramified
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_basis_integral_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → (¬ ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1) → IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (2 * i))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadField.inert_content | exact GlobalTheory.CompanionTheory.SW.QuadField.inert_content | (intros; apply GlobalTheory.CompanionTheory.SW.QuadField.inert_content <;> assumption)
