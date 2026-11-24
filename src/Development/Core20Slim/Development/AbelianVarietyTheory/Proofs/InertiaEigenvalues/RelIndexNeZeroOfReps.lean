module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.FormInner

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}






theorem classSum_transport {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I]
    (ι : Γ →* G) (hι : Function.Injective ι) (φ : GAf L n ≃* G) (hrat : ∀ h, h ∈ GQ L n ↔ ∃ γ, ι γ = φ h)
    (J : Subgroup G) (y : I → G) (hy : Formalism.IndefR.Bridge.IsReps ι J y) :
    ∃ T, IsClassReps (J.comap φ.toMonoidHom) T ∧ ∀ (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (f f' : GAf L n → a.W)
      (F F' : G → W), (∀ g, β (f g) (f' g) = inner ℂ (F (φ g)) (F' (φ g))) →
      classSum a β (J.comap φ.toMonoidHom) T f f' = Formalism.IndefR.Bridge.adInner ι J y F F' := by
  classical
  have hinj : Function.Injective fun i => φ.symm (y i) := fun i j e => by
    have e' : y i = y j := φ.symm.injective e
    exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [e']⟩
  have key : ∀ g i, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J.comap φ.toMonoidHom ∧ g = (γ : GAf L n) * φ.symm (y i) * κ) ↔
      ∃ (γ : Γ) (k : J), φ g = ι γ * y i * k := fun g i => by
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
      exact ⟨δ, ⟨φ κ, hκ⟩, by simp [hδ]⟩
    · rintro ⟨γ, k, e⟩
      refine ⟨⟨φ.symm (ι γ), (hrat _).2 ⟨γ, by simp⟩⟩, φ.symm k, by simp, φ.injective (by simp [e])⟩
  refine ⟨Finset.univ.image fun i => φ.symm (y i), fun g => ?_, fun a β f f' F F' h => ?_⟩
  · obtain ⟨i, hi, hu⟩ := hy (φ g)
    refine ⟨φ.symm (y i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 hi⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hu j ((key g j).1 h)]
  · rw [classSum, Finset.sum_image fun i _ j _ e => hinj e, Formalism.IndefR.Bridge.adInner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h, MulEquiv.apply_symm_apply]
    congr 3
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun δ : Formalism.IndefR.Bridge.stab ι J (y i) =>
      (⟨⟨φ.symm (ι δ), (hrat _).2 ⟨δ, by simp⟩⟩, by simpa using (Formalism.IndefR.Bridge.mem_stab ι).1 δ.2⟩ :
        {γ : GQ L n // (φ.symm (y i))⁻¹ * (γ : GAf L n) * φ.symm (y i) ∈ J.comap φ.toMonoidHom})) ⟨fun δ δ' e => ?_, fun γ => ?_⟩)
    · exact Subtype.ext (hι (φ.symm.injective (congrArg (fun z => (z.1 : GAf L n)) e)))
    · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.1.2
      refine ⟨⟨δ, (Formalism.IndefR.Bridge.mem_stab ι).2 ?_⟩, Subtype.ext (Subtype.ext (by simp [hδ]))⟩
      simpa [hδ] using γ.2

end GlobalTheory.FormInner

end
