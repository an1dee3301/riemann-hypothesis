module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuLR

open Filter
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem cofinite_le_principal_compl :
    cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff]; exact S.finite_toSet.compl_mem_cofinite


open Classical in
def jSP : SPart F S × OPart F S →
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  fun p => ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v), by
    rw [eventually_principal]
    intro v hv
    have hv' : v ∉ S := hv
    simp only [dif_neg hv']
    exact (p.2 ⟨v, hv'⟩).2⟩

def jSPinv : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] →
    SPart F S × OPart F S :=
  fun x => (fun v => x v.1, fun v => ⟨x v.1, x.2 v.2⟩)

theorem continuous_jSP : Continuous (jSP F S) := by
  rw [RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff]
  refine continuous_pi fun v => ?_
  by_cases h : v ∈ S
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => p.1 ⟨v, h⟩ := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact (continuous_apply _).comp continuous_fst
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)

theorem continuous_jSPinv : Continuous (jSPinv F S) := by
  have hc : Continuous (fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] =>
      (x : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F)) :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous
  refine Continuous.prodMk (continuous_pi fun v => (continuous_apply v.1).comp hc)
    (continuous_pi fun v => ((continuous_apply v.1).comp hc).subtype_mk _)

def jSPHomeo : SPart F S × OPart F S ≃ₜ
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] where
  toFun := jSP F S
  invFun := jSPinv F S
  left_inv p := by
    ext v
    · simp [jSP, jSPinv, v.2]
    · simp [jSP, jSPinv, v.2]
  right_inv x := by
    ext v
    by_cases h : v ∈ S <;> simp [jSP, jSPinv, h]
  continuous_toFun := continuous_jSP F S
  continuous_invFun := continuous_jSPinv F S

theorem jS_eq_comp : (jS F S : SPart F S × OPart F S → Af F) =
    RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl F S) ∘ jSP F S := by
  funext p; rfl

theorem isOpenEmbedding_jS : IsOpenEmbedding (jS F S) := by
  rw [jS_eq_comp]
  exact (RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F)) (cofinite_le_principal_compl F S)).comp
    (jSPHomeo F S).isOpenEmbedding

end GlobalTheory.ModuLR
