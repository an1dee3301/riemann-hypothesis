module

public import Mathlib
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

namespace GroundTheory.ProfCoh

universe w u v

section IntRep

variable {G : Type v} [Monoid G]

def intRep {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) :
    Representation (ULift.{w} ℤ) G V where
  toFun g :=
    { toFun := φ g
      map_add' := map_add (φ g)
      map_smul' := fun r x => by
        change φ g (r.down • x) = r.down • φ g x
        exact map_zsmul (φ g) r.down x }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

def intRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation (ULift.{w} ℤ) G (Additive M) :=
  intRep.{w} ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

def zRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation ℤ G (Additive M) :=
  (addMonoidEndRingEquivInt (Additive M) : AddMonoid.End (Additive M) →* _).comp
    ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

end IntRep

section Galois

variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]

def galUnitsHom : Gal(L/K) →* Monoid.End Lˣ where
  toFun σ := Units.map (σ : L →* L)
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

@[simp]
theorem coe_galUnitsHom_apply (σ : Gal(L/K)) (u : Lˣ) :
    ((galUnitsHom K L σ u : Lˣ) : L) = σ u :=
  rfl

def galRootsOfUnityHom (n : ℕ) : Gal(L/K) →* Monoid.End (rootsOfUnity n L) where
  toFun σ := restrictRootsOfUnity σ n
  map_one' := by
    ext ζ
    rfl
  map_mul' σ τ := by
    ext ζ
    rfl

@[simp]
theorem coe_galRootsOfUnityHom_apply (n : ℕ) (σ : Gal(L/K)) (ζ : rootsOfUnity n L) :
    (((galRootsOfUnityHom K L n σ ζ : Lˣ)) : L) = σ (ζ : Lˣ) :=
  rfl



abbrev galUnits : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galUnitsHom K L))

abbrev galRootsOfUnity (n : ℕ) : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galRootsOfUnityHom K L n))

abbrev galUnitsZ : Rep.{u} ℤ Gal(L/K) := Rep.of (zRepOfMonoidEnd (galUnitsHom K L))

variable {K L}

@[simp]
theorem galUnits_ρ_apply (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnits.{w} K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) :=
  rfl

@[simp]
theorem galUnitsZ_ρ_apply (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnitsZ K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) :=
  rfl

@[simp]
theorem galRootsOfUnity_ρ_apply (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnity.{w} K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) :=
  rfl

end Galois

end GroundTheory.ProfCoh
