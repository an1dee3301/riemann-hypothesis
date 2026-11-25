module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
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
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.ConjCoordDenom

theorem exists_common_denom_conj_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), (∀ x, w.valuation E (σ x) = w.valuation E x) →
    (∀ a : E, w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r) →
    ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → ∀ (X : Matrix (Fin n) (Fin n) E),
    (∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) →
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r := by
  intro F E _ _ _ _ _ σ w hσ hden n L hL X hX
  obtain ⟨S, hS⟩ := hL
  have key : ∀ g ∈ S, ∀ i, ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ g) i) = r := by
    intro g hg i
    apply hden
    rw [hσ]
    exact hX g (hS ▸ Submodule.subset_span hg) i
  choose! d hd r hr using key
  haveI := w.isPrime
  refine ⟨∏ g ∈ S, ∏ i, d g i, ?_, ?_⟩
  · intro hmem
    obtain ⟨g, hg, hmem⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    obtain ⟨i, -, hmem⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact hd g hg i hmem
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro i
      obtain ⟨t, ht⟩ : d g i ∣ ∏ g ∈ S, ∏ i, d g i :=
        (Finset.dvd_prod_of_mem (fun i => d g i) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun g => ∏ i, d g i) hg)
      refine ⟨t * r g i, ?_⟩
      rw [ht]
      push_cast
      rw [mul_comm (d g i : E), mul_assoc, hr g hg i]
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨b, hb⟩ := hy i
      refine ⟨a + b, ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, map_add (f := _), mul_add, ha, hb]
      push_cast
      rfl
    | smul c x _ hx =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      refine ⟨NumberField.RingOfIntegers.mapRingHom σ.toRingHom c * a, ?_⟩
      have hc : c • x = (c : E) • x := (algebraMap_smul E c x).symm
      rw [hc, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm, ha]
      push_cast
      rfl

end GlobalTheory.ConjCoordDenom
