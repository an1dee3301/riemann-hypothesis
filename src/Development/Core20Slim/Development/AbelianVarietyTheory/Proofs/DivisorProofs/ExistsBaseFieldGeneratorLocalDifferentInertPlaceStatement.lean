module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseFieldGeneratorLocalDifferentInertPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
public import Formalism.SatakeDualWeyl.StatementG
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseField_generator_localDifferent_inertPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  first | exact @GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | exact GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt | (intros; apply GlobalTheory.InertDifferentGen.exists_generator_different_of_isInertAt <;> assumption)
