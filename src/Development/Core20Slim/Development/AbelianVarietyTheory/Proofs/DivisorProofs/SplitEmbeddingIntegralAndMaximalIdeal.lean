module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem GlobalTheory.adicEmbedding_integral_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) :
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  set O := v.adicCompletionIntegers F
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O := by
    have := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
    exact this
  have ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1 := by
    intro a
    have h1 : IsIntegral ℤ (τ a) := IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)
    have h2 : IsIntegral O (τ a) := h1.tower_top
    exact hv.mem_of_integral h2
  refine ⟨ha, ?_⟩
  let φ : 𝓞 E →+* O :=
    ((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring
      (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))
  have hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1 := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    change ¬ Valued.v (τ a) = 1 ↔ _
    exact ⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩
  refine ⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩
  apply Ideal.IsPrime.isMaximal inferInstance
  intro hbot
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at this
    exact this
  have hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0 := by
    intro h
    apply hπ0
    apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    simpa using h
  apply hne
  have : algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ := by
    rw [hmem]
    have e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F) := by
      exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)
    rw [e, AlgHom.commutes]
    exact hlt
  rw [hbot] at this
  simpa using this
