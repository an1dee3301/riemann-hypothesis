module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open NumberField

namespace GlobalTheory.ThetaParseval

def ratVec (F : Type) [Field F] [NumberField F] (κ : Type) : AddSubgroup (κ → AdeleRing (𝓞 F) F) :=
  (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).range

theorem mem_ratVec_iff {F : Type} [Field F] [NumberField F] {κ : Type} (x : κ → AdeleRing (𝓞 F) F) :
    x ∈ ratVec F κ ↔ ∃ ξ : κ → F, x = fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i) := by
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩

end GlobalTheory.ThetaParseval

end
