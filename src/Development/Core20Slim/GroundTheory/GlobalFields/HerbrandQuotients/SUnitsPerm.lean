module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.Permutation
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.LatticeBridge
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Quot
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Separable
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.SetTheory.Cardinal.Finite

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open MulAction NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

section FunPerm

variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X]

def funPermRep : Representation k G (X → k) where
  toFun g := LinearMap.funLeft k k (fun x => g⁻¹ • x)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, mul_smul]

variable {k G X}

@[simp]
theorem funPermRep_apply (g : G) (f : X → k) (x : X) : funPermRep k G X g f x = f (g⁻¹ • x) :=
  rfl

def funEquivMonoidAlgebra [Finite X] : (X → ℤ) ≃+ MonoidAlgebra ℤ X where
  toFun := permOfFun
  invFun f x := f.coeff x
  left_inv F := funext fun x => coeff_permOfFun F x
  right_inv f := by
    ext x
    exact coeff_permOfFun _ x
  map_add' F F' := by
    ext x
    simp

theorem funEquivMonoidAlgebra_funPermRep [Finite X] (g : G) (F : X → ℤ) :
    funEquivMonoidAlgebra (funPermRep ℤ G X g F) =
      Representation.ofMulAction ℤ G X g (funEquivMonoidAlgebra F) := by
  ext x
  change (permOfFun _).coeff x = _
  rw [coeff_permOfFun, Representation.coeff_ofMulAction]
  change _ = (permOfFun F).coeff _
  rw [coeff_permOfFun, funPermRep_apply]

theorem cycHerbrand_funPermRep [Fintype G] [Finite X] [Fintype (orbitRel.Quotient G X)] {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (funPermRep ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by
  rw [cycHerbrand_congr funEquivMonoidAlgebra funEquivMonoidAlgebra_funPermRep σ,
    ← cyclicHerbrand_eq_cycHerbrand, cyclicHerbrand_ofMulAction hσ]

end FunPerm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section Infinite

open scoped Classical in
theorem prod_card_stabilizer_infinitePlace
    [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L))] :
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L),
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) := by
  classical
  refine Fintype.prod_equiv InfinitePlace.orbitRelEquiv _ _ fun ω => ?_
  have h1 : InfinitePlace.orbitRelEquiv ω = (Quotient.out ω).comap (algebraMap K L) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  rw [h1, InfinitePlace.card_stabilizer, InfinitePlace.isUnramifiedIn_comap]
  split_ifs <;> simp

end Infinite

section Finite

def placeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  ⟨w.asIdeal.under (𝓞 K), inferInstance, Ideal.under_ne_bot (𝓞 K) w.ne_bot⟩

instance (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (placeBelow (K := K) w).asIdeal :=
  ⟨rfl⟩


omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem eq_placeBelow_of_liesOver {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (h : w.asIdeal.LiesOver v.asIdeal) : v = placeBelow w :=
  HeightOneSpectrum.ext h.over

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem placeBelow_smul (g : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    placeBelow (K := K) (g • w) = placeBelow w := by
  have h : (g • w.asIdeal).LiesOver (placeBelow (K := K) w).asIdeal := inferInstance
  exact HeightOneSpectrum.ext h.over.symm

variable (S : Set (HeightOneSpectrum (𝓞 L)))

@[reducible] def stableMulAction (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) : MulAction (L ≃ₐ[K] L) S where
  smul g w := ⟨g • w.1, hS g w.1 w.2⟩
  one_smul w := Subtype.ext (one_smul _ w.1)
  mul_smul g h w := Subtype.ext (mul_smul g h w.1)

theorem prod_card_stabilizer_finitePlace (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    letI _ := stableMulAction S hS
    ∀ [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S)],
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) S,
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ) := by
  let _ := stableMulAction S hS
  intro _
  have hstab : ∀ x : S, Nat.card (stabilizer (L ≃ₐ[K] L) x) =
      (placeBelow (K := K) x.1).asIdeal.ramificationIdxIn (𝓞 L) *
        (placeBelow (K := K) x.1).asIdeal.inertiaDegIn (𝓞 L) := by
    intro x
    have h1 : stabilizer (L ≃ₐ[K] L) x = stabilizer (L ≃ₐ[K] L) x.1.asIdeal := by
      ext g
      rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff]
      exact ⟨fun h => congrArg HeightOneSpectrum.asIdeal h, fun h => HeightOneSpectrum.ext h⟩
    rw [h1]
    exact Ideal.card_stabilizer_eq (placeBelow (K := K) x.1).asIdeal x.1.asIdeal
  rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
  refine finprod_mem_eq_of_bijOn (M := ℚ)
    (t := {v : HeightOneSpectrum (𝓞 K) | ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal})
    (fun ω : orbitRel.Quotient (L ≃ₐ[K] L) S => placeBelow (K := K) (Quotient.out ω).1)
    ⟨?_, ?_, ?_⟩ ?_
  · intro ω _
    exact ⟨(Quotient.out ω).1, (Quotient.out ω).2, inferInstance⟩
  · intro ω₁ _ ω₂ _ h
    simp only at h
    set x₁ := Quotient.out ω₁
    set x₂ := Quotient.out ω₂
    let _ : x₁.1.asIdeal.LiesOver (placeBelow (K := K) x₂.1).asIdeal := by
      rw [← h]
      infer_instance
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      (placeBelow (K := K) x₂.1).asIdeal x₂.1.asIdeal x₁.1.asIdeal (L ≃ₐ[K] L)
    rw [← Quotient.out_eq ω₁, ← Quotient.out_eq ω₂]
    exact Quotient.sound ⟨g, Subtype.ext (HeightOneSpectrum.ext hg)⟩
  · rintro v ⟨w, hw, hlies⟩
    refine ⟨Quotient.mk _ ⟨w, hw⟩, Set.mem_univ _, ?_⟩
    obtain ⟨g, hg⟩ : Quotient.out (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩) ∈
        orbit (L ≃ₐ[K] L) (⟨w, hw⟩ : S) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩))
    simp only
    rw [← hg]
    change placeBelow (g • w) = v
    rw [placeBelow_smul, ← eq_placeBelow_of_liesOver hlies]
  · intro ω _
    rw [hstab]

end Finite

end

end GroundTheory.Global
