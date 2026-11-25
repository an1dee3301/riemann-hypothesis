module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse

@[expose] public section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat

variable {E : Type} [Field E] [NumberField E]

def scLat {n : ℕ} (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ}
  zero_mem' := fun c _ => by rw [smul_zero]; exact Λ.zero_mem
  add_mem' := fun hx hy c hc => by rw [smul_add]; exact Λ.add_mem (hx c hc) (hy c hc)
  smul_mem' := fun r y hy c hc => by rw [smul_comm]; exact Λ.smul_mem r (hy c hc)

theorem mem_scLat {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} :
    y ∈ scLat 𝔞 Λ ↔ ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ := Iff.rfl

def blkA {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin a → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inl)

def blkB {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin b → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inr)

def pairLat {a b d : ℕ} (ΛA : Submodule (𝓞 E) (Fin a → E)) (ΛB : Submodule (𝓞 E) (Fin b → E))
    (e : Fin a ⊕ Fin b ≃ Fin d) : Submodule (𝓞 E) (Fin d → E) :=
  ΛA.comap (blkA e) ⊓ ΛB.comap (blkB e)

theorem mem_pairLat {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}
    {e : Fin a ⊕ Fin b ≃ Fin d} {x : Fin d → E} :
    x ∈ pairLat ΛA ΛB e ↔ (fun k => x (e (.inl k))) ∈ ΛA ∧ (fun k => x (e (.inr k))) ∈ ΛB := Iff.rfl

end GlobalTheory.SkewLat

end
