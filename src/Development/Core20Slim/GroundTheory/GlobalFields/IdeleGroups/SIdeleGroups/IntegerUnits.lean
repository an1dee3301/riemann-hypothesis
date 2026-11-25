module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Places
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.StandardOpenEquiv
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Valuation.ValuationSubring

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup


omit [NumberField K] in
theorem smul_mem_standardOpenSubgroup (σ : L ≃ₐ[K] L) {x : IdeleGroup L}
    (hx : x ∈ standardOpenSubgroup L) : σ • x ∈ standardOpenSubgroup L := by
  rw [mem_standardOpenSubgroup_iff_ord] at hx ⊢
  intro w
  rw [ord_smul]
  exact hx _

variable (v : HeightOneSpectrum (𝓞 K))

def integerUnitsAboveIncl :
    ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) →*
      ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  MonoidHom.pi fun w ↦
    (Units.map (w.1.adicCompletionIntegers L).subtype.toMonoidHom).comp (Pi.evalMonoidHom _ w)

omit [NumberField K] in
@[simp]
theorem coe_integerUnitsAboveIncl_apply
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v) :
    ((integerUnitsAboveIncl v z w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      ((z w : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) :=
  rfl

omit [NumberField K] in
theorem integerUnitsAboveIncl_injective :
    Function.Injective (integerUnitsAboveIncl (L := L) v) := fun _ _ h ↦
  funext fun w ↦ Units.ext (Subtype.ext (congrArg (fun y ↦ ((y w : (w.1.adicCompletion L)ˣ) :
    w.1.adicCompletion L)) h))


omit [NumberField K] in
theorem mem_range_integerUnitsAboveIncl_iff (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    y ∈ (integerUnitsAboveIncl v).range ↔ ∀ w : PlacesOver L v,
      (y w : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L ∧
        ((y w)⁻¹ : (w.1.adicCompletion L)ˣ).val ∈ w.1.adicCompletionIntegers L := by
  constructor
  · rintro ⟨z, rfl⟩ w
    exact ⟨(z w : w.1.adicCompletionIntegers L).2,
      (((z w)⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L).2⟩
  · intro h
    refine ⟨fun w ↦ ⟨⟨y w, (h w).1⟩, ⟨((y w)⁻¹ : (w.1.adicCompletion L)ˣ), (h w).2⟩,
      Subtype.ext (y w).mul_inv, Subtype.ext (y w).inv_mul⟩, ?_⟩
    funext w
    exact Units.ext rfl

theorem finiteEmbedAbove_integerUnitsAboveIncl_mem
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    finiteEmbedAbove v (integerUnitsAboveIncl v z) ∈ standardOpenSubgroup L := by
  refine (mem_standardOpenSubgroup L).2 fun w ↦ ?_
  rw [← map_inv]
  by_cases h : w.asIdeal.LiesOver v.asIdeal
  · rw [coe_finiteEmbedAbove_snd v _ ⟨w, h⟩, coe_finiteEmbedAbove_snd v _ ⟨w, h⟩]
    exact ⟨(z ⟨w, h⟩ : w.adicCompletionIntegers L).2,
      (((z ⟨w, h⟩)⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L).2⟩
  · rw [coe_finiteEmbedAbove_snd_of_not v _ h, coe_finiteEmbedAbove_snd_of_not v _ h]
    exact ⟨(w.adicCompletionIntegers L).one_mem, (w.adicCompletionIntegers L).one_mem⟩

def integerUnitsAboveSmul (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ :=
  fun w ↦ localIntegerUnit w.1 ⟨σ • finiteEmbedAbove v (integerUnitsAboveIncl v z),
    smul_mem_standardOpenSubgroup σ (finiteEmbedAbove_integerUnitsAboveIncl_mem v z)⟩

instance : SMul (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :=
  ⟨integerUnitsAboveSmul v⟩

theorem integerUnitsAboveIncl_smul (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    integerUnitsAboveIncl v (σ • z) = σ • integerUnitsAboveIncl v z :=
  funext fun _ ↦ Units.ext rfl

instance integerUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :=
  (integerUnitsAboveIncl_injective v).mulDistribMulAction (integerUnitsAboveIncl v)
    (integerUnitsAboveIncl_smul v)

theorem integerUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v) :
    ((((σ • z) (σ • w) : ((σ • w).1.adicCompletionIntegers L)ˣ) :
      (σ • w).1.adicCompletionIntegers L) : (σ • w).1.adicCompletion L) =
      galEquiv v σ w.1 (σ • w).1 rfl ((z w : w.1.adicCompletionIntegers L) :
        w.1.adicCompletion L) := by
  rw [← coe_integerUnitsAboveIncl_apply, integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply,
    coe_integerUnitsAboveIncl_apply]

end IdeleGroup

end

end GroundTheory.Global
