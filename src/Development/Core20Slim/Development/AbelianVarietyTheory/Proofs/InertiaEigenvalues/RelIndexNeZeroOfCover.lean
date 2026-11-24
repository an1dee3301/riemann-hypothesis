module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.ClassPet

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}








end GlobalTheory.ClassPet

namespace GlobalTheory.ClassPet

section Grp
variable {G : Type*} [Group G]

theorem relIndex_ne_zero_of_cover {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H)
    (hle : H ≤ K) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    let φ : F → K ⧸ H.subgroupOf K := fun f =>
      if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)
    refine Finite.of_surjective φ (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H κ =>
      obtain ⟨f, hf, hfκ⟩ := hF κ κ.2
      have hfK : f ∈ K := by
        have := K.mul_mem κ.2 (K.inv_mem (hle hfκ))
        simpa using this
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [φ, dif_pos hfK]
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem exists_cosetReps {H K : Subgroup G} (hle : H ≤ K) (hne : H.relIndex K ≠ 0) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ K) ∧ (∀ κ ∈ K, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H) ∧ F.card = H.relIndex K := by
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let o : K ⧸ H.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have ho : Function.Injective o := by
    intro q q' h
    have : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (Quotient.out q).2
  · intro κ hκ
    refine ⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))
      simpa [Subgroup.mem_subgroupOf, o] using h
    · rintro u ⟨hu, hu'⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have : q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K) := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')
      rw [this]
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ]
    show _ = (H.subgroupOf K).index
    rw [Subgroup.index, Nat.card_eq_fintype_card]


end Grp

section Sum
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
  (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))






end Sum

end GlobalTheory.ClassPet
