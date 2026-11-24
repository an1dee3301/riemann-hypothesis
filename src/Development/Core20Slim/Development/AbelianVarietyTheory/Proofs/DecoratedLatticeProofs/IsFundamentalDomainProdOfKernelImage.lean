module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Init.Tactics
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AEDisjoint
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Filter.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

theorem isFundamentalDomain_prod_of_ker_image : ∀ (N G : Type) [Group N] [Group G] [MeasurableSpace N] [MeasurableSpace G] [MeasurableMul N] [MeasurableMul G] (ν : Measure N) (μ : Measure G) [SFinite ν] [SFinite μ] [ν.IsMulLeftInvariant] [μ.IsMulLeftInvariant] (Γ : Subgroup (N × G)) [Countable Γ] (𝓐 : Set N) (𝓑 : Set G), IsFundamentalDomain (Γ.comap (MonoidHom.inl N G)) 𝓐 ν → IsFundamentalDomain (Γ.map (MonoidHom.snd N G)) 𝓑 μ → IsFundamentalDomain Γ (𝓐 ×ˢ 𝓑) (ν.prod μ) := by
  intro N G _ _ _ _ _ _ ν μ _ _ _ _ Γ _ 𝓐 𝓑 hA hB
  classical

  have hKc : Countable (Γ.comap (MonoidHom.inl N G)) := by
    refine Function.Injective.countable (f := fun k : Γ.comap (MonoidHom.inl N G) =>
      (⟨MonoidHom.inl N G k, k.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun x : Γ => (x : N × G).1) hab
    simpa using this
  have hHc : Countable (Γ.map (MonoidHom.snd N G)) := by
    refine Function.Surjective.countable (f := fun γ : Γ =>
      (⟨(γ : N × G).2, Subgroup.mem_map_of_mem _ γ.2⟩ : Γ.map (MonoidHom.snd N G))) ?_
    rintro ⟨h, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

  have hlift : ∀ h : Γ.map (MonoidHom.snd N G), ∃ m : N, ((m, (h : G)) : N × G) ∈ Γ := by
    rintro ⟨h, x, hx, rfl⟩
    exact ⟨x.1, by simpa using hx⟩
  choose mm hmm using hlift

  have memS : ∀ (γ : Γ) (p : N × G), p ∈ γ • (𝓐 ×ˢ 𝓑) →
      ((γ : N × G).1⁻¹ * p.1 ∈ 𝓐 ∧ (γ : N × G).2⁻¹ * p.2 ∈ 𝓑) := by
    rintro γ p ⟨q, hq, rfl⟩
    simpa [Subgroup.smul_def] using hq
  refine
    { nullMeasurableSet := hA.nullMeasurableSet.prod hB.nullMeasurableSet
      ae_covers := ?_
      aedisjoint := ?_ }
  · have h2 : ∀ᵐ g ∂μ, ∃ h : Γ.map (MonoidHom.snd N G), h • g ∈ 𝓑 := hB.ae_covers
    have h1 : ∀ᵐ n ∂ν, ∀ h : Γ.map (MonoidHom.snd N G),
        ∃ k : Γ.comap (MonoidHom.inl N G), k • (mm h * n) ∈ 𝓐 := by
      rw [ae_all_iff]
      intro h
      exact (measurePreserving_mul_left ν (mm h)).quasiMeasurePreserving.ae hA.ae_covers
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
      Measure.quasiMeasurePreserving_snd.ae h2] with p hn hg
    obtain ⟨h, hh⟩ := hg
    obtain ⟨k, hk⟩ := hn h
    have hk' : (((k : N), (1 : G)) : N × G) ∈ Γ := k.2
    refine ⟨⟨((k : N), (1 : G)) * (mm h, (h : G)), Γ.mul_mem hk' (hmm h)⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [Subgroup.smul_def, mul_assoc] using hk
    · simpa [Subgroup.smul_def] using hh
  · intro γ γ' hne
    change (ν.prod μ) ((γ • (𝓐 ×ˢ 𝓑)) ∩ (γ' • (𝓐 ×ˢ 𝓑))) = 0
    by_cases hh : (γ : N × G).2 = (γ' : N × G).2
    ·
      have hkmem : MonoidHom.inl N G ((γ' : N × G).1⁻¹ * (γ : N × G).1) ∈ Γ := by
        have e : MonoidHom.inl N G ((γ' : N × G).1⁻¹ * (γ : N × G).1) = ((γ'⁻¹ * γ : Γ) : N × G) := by
          ext <;> simp [hh]
        rw [e]; exact (γ'⁻¹ * γ).2
      let k : Γ.comap (MonoidHom.inl N G) := ⟨(γ' : N × G).1⁻¹ * (γ : N × G).1, hkmem⟩
      have hk1 : (1 : Γ.comap (MonoidHom.inl N G)) ≠ k⁻¹ := by
        intro h1
        apply hne
        have h1' : (γ' : N × G).1⁻¹ * (γ : N × G).1 = 1 := by
          have := congrArg (fun x : Γ.comap (MonoidHom.inl N G) => ((x⁻¹ : Γ.comap (MonoidHom.inl N G)) : N)) h1
          simpa [k] using this.symm
        apply Subtype.ext
        exact Prod.ext (inv_mul_eq_one.mp h1').symm hh
      have hnull : ν (𝓐 ∩ k⁻¹ • 𝓐) = 0 := by
        have := hA.aedisjoint hk1
        simpa [Function.onFun, AEDisjoint] using this
      refine measure_mono_null (t := Prod.fst ⁻¹' ((fun x => (γ : N × G).1⁻¹ * x) ⁻¹' (𝓐 ∩ k⁻¹ • 𝓐))) ?_
        (Measure.quasiMeasurePreserving_fst.preimage_null
          ((measurePreserving_mul_left ν (γ : N × G).1⁻¹).quasiMeasurePreserving.preimage_null hnull))
      rintro p ⟨hp, hp'⟩
      obtain ⟨a1, -⟩ := memS γ p hp
      obtain ⟨a2, -⟩ := memS γ' p hp'
      refine ⟨a1, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Subgroup.smul_def, smul_eq_mul]
      show ((γ' : N × G).1⁻¹ * (γ : N × G).1) * ((γ : N × G).1⁻¹ * p.1) ∈ 𝓐
      simpa [mul_assoc] using a2
    ·
      let h : Γ.map (MonoidHom.snd N G) := ⟨(γ : N × G).2, Subgroup.mem_map_of_mem _ γ.2⟩
      let h' : Γ.map (MonoidHom.snd N G) := ⟨(γ' : N × G).2, Subgroup.mem_map_of_mem _ γ'.2⟩
      have hne' : h ≠ h' := fun e => hh (congrArg Subtype.val e)
      have hnull : μ ((h • 𝓑) ∩ (h' • 𝓑)) = 0 := hB.aedisjoint hne'
      refine measure_mono_null (t := Prod.snd ⁻¹' ((h • 𝓑) ∩ (h' • 𝓑))) ?_
        (Measure.quasiMeasurePreserving_snd.preimage_null hnull)
      rintro p ⟨hp, hp'⟩
      refine ⟨?_, ?_⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
        simpa [h] using (memS γ p hp).2
      · rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
        simpa [h'] using (memS γ' p hp').2

end GlobalTheory
