module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
public import Batteries.Logic
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.CosetTop

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    Valued.v (algebraMap F (Fv F v) z) = v.valuation F z := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    algebraMap F (Fv F v) z ∈ v.adicCompletionIntegers F ↔ v.valuation F z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]

theorem locMem_top_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by
  constructor
  · rintro ⟨s, hs, y, -, h⟩
    have h1 : v.valuation F (s : F) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 : v.valuation F (s : F) * v.valuation F z = v.valuation F (y : F) := by
      rw [← map_mul, h]
    rw [h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one v y
  · intro hz
    have hmem : z ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hz
    obtain ⟨a, s, hs, h⟩ := hmem
    refine ⟨s, hs, a, Submodule.mem_top, ?_⟩
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this]
      exact v.asIdeal.zero_mem
    rw [h]
    change (s : F) * ((a : F) * (s : F)⁻¹) = a
    field_simp

theorem cosetOff_top : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  intro F _ _ ι S
  ext x
  simp only [cosetOff, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, locMem_top_iff, algebraMap_mem_iff]

end GlobalTheory.CompanionTheory.Equi.CosetTop
end
