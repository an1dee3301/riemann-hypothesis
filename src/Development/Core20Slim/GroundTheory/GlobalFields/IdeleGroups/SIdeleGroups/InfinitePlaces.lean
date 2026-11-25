module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Places
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

section Infinite

variable (v : InfinitePlace K)


open Classical in
def infiniteAdeleAboveFun (a : (w : v.placesOver L) → w.1.Completion) (w : InfinitePlace L) :
    w.Completion :=
  if h : w ∈ v.placesOver L then a ⟨w, h⟩ else 1

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_apply (a : (w : v.placesOver L) → w.1.Completion)
    (w : v.placesOver L) : infiniteAdeleAboveFun v a w.1 = a w := by
  rw [infiniteAdeleAboveFun, dite_eq_left w.2]

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_apply_of_not (a : (w : v.placesOver L) → w.1.Completion)
    {w : InfinitePlace L} (h : w ∉ v.placesOver L) : infiniteAdeleAboveFun v a w = 1 := by
  rw [infiniteAdeleAboveFun, dite_eq_right h]

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_one :
    infiniteAdeleAboveFun v (1 : (w : v.placesOver L) → w.1.Completion) = 1 := by
  funext w
  by_cases h : w ∈ v.placesOver L
  · exact infiniteAdeleAboveFun_apply v 1 ⟨w, h⟩
  · exact infiniteAdeleAboveFun_apply_of_not v 1 h

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_mul (a b : (w : v.placesOver L) → w.1.Completion) :
    infiniteAdeleAboveFun v (a * b) = infiniteAdeleAboveFun v a * infiniteAdeleAboveFun v b := by
  funext w
  rw [Pi.mul_apply]
  by_cases h : w ∈ v.placesOver L
  · rw [infiniteAdeleAboveFun_apply v _ ⟨w, h⟩, infiniteAdeleAboveFun_apply v _ ⟨w, h⟩,
      infiniteAdeleAboveFun_apply v _ ⟨w, h⟩, Pi.mul_apply]
  · rw [infiniteAdeleAboveFun_apply_of_not v _ h, infiniteAdeleAboveFun_apply_of_not v _ h,
      infiniteAdeleAboveFun_apply_of_not v _ h, mul_one]

def infiniteAdeleAbove : ((w : v.placesOver L) → w.1.Completion) →* InfiniteAdeleRing L where
  toFun a := infiniteAdeleAboveFun v a
  map_one' := infiniteAdeleAboveFun_one v
  map_mul' a b := infiniteAdeleAboveFun_mul v a b

def infiniteEmbedAbove : ((w : v.placesOver L) → (w.1.Completion)ˣ) →* IdeleGroup L :=
  (Units.map (MonoidHom.prod (infiniteAdeleAbove v) 1 :
      ((w : v.placesOver L) → w.1.Completion) →*
        InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L)).comp
    (MulEquiv.piUnits (M := fun w : v.placesOver L ↦ w.1.Completion)).symm.toMonoidHom


omit [NumberField K] in
theorem coe_infiniteEmbedAbove_fst (y : (w : v.placesOver L) → (w.1.Completion)ˣ)
    (w : v.placesOver L) : ((infiniteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).1 w.1 = y w :=
  infiniteAdeleAboveFun_apply v _ w


def infiniteProjAbove : IdeleGroup L →* ((w : v.placesOver L) → (w.1.Completion)ˣ) :=
  MonoidHom.pi fun w ↦ infiniteProj w.1

omit [NumberField K] in
@[simp]
theorem coe_infiniteProjAbove_apply (x : IdeleGroup L) (w : v.placesOver L) :
    ((infiniteProjAbove v x w : (w.1.Completion)ˣ) : w.1.Completion) = (x : 𝔸[L]).1 w.1 :=
  rfl

omit [NumberField K] in
theorem infiniteProjAbove_infiniteEmbedAbove (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteProjAbove v (infiniteEmbedAbove v y) = y :=
  funext fun w ↦ Units.ext (coe_infiniteEmbedAbove_fst v y w)


omit [NumberField K] [NumberField L] in
theorem comap_mem_placesOver (σ : L ≃ₐ[K] L) (w : v.placesOver L) :
    w.1.comap ((σ : L ≃+* L) : L →+* L) ∈ v.placesOver L := by
  rw [comap_eq_inv_smul]
  exact (σ⁻¹ • w).2



omit [NumberField K] in
theorem infiniteProjAbove_smul_congr (σ : L ≃ₐ[K] L) {x y : IdeleGroup L}
    (h : infiniteProjAbove v x = infiniteProjAbove v y) :
    infiniteProjAbove v (σ • x) = infiniteProjAbove v (σ • y) := by
  funext u
  refine Units.ext ?_
  rw [coe_infiniteProjAbove_apply, coe_infiniteProjAbove_apply, coe_smul_idele, coe_smul_idele,
    smul_fst, smul_fst]
  congr 1
  exact congrArg (fun f : (w : v.placesOver L) → (w.1.Completion)ˣ ↦
    ((f ⟨u.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ u⟩ : _) :
      (u.1.comap ((σ : L ≃+* L) : L →+* L)).Completion)) h

instance infiniteUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : v.placesOver L) → (w.1.Completion)ˣ) where
  smul σ y := infiniteProjAbove v (σ • infiniteEmbedAbove v y)
  one_smul y := by
    change infiniteProjAbove v ((1 : L ≃ₐ[K] L) • infiniteEmbedAbove v y) = y
    rw [one_smul, infiniteProjAbove_infiniteEmbedAbove]
  mul_smul σ τ y := by
    change infiniteProjAbove v ((σ * τ) • infiniteEmbedAbove v y) =
      infiniteProjAbove v
        (σ • infiniteEmbedAbove v (infiniteProjAbove v (τ • infiniteEmbedAbove v y)))
    rw [mul_smul]
    exact infiniteProjAbove_smul_congr v σ (infiniteProjAbove_infiniteEmbedAbove v _).symm
  smul_mul σ y z := by
    change infiniteProjAbove v (σ • infiniteEmbedAbove v (y * z)) =
      infiniteProjAbove v (σ • infiniteEmbedAbove v y) *
        infiniteProjAbove v (σ • infiniteEmbedAbove v z)
    rw [map_mul, smul_mul', map_mul]
  smul_one σ := by
    change infiniteProjAbove v (σ • infiniteEmbedAbove v 1) = 1
    rw [map_one, smul_one, map_one]

theorem infiniteUnitsAbove_smul_def (σ : L ≃ₐ[K] L)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    σ • y = infiniteProjAbove v (σ • infiniteEmbedAbove v y) :=
  rfl

theorem infiniteProjAbove_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    infiniteProjAbove v (σ • x) = σ • infiniteProjAbove v x :=
  infiniteProjAbove_smul_congr v σ (infiniteProjAbove_infiniteEmbedAbove v _).symm







theorem infiniteUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (w : v.placesOver L) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1
        (y ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩) := by
  rw [infiniteUnitsAbove_smul_def, coe_infiniteProjAbove_apply, coe_smul_idele, smul_fst,
    coe_infiniteEmbedAbove_fst v y ⟨_, comap_mem_placesOver v σ w⟩]

end Infinite

end IdeleGroup

end

end GroundTheory.Global
