module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Batteries.Logic
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Push

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory

theorem exists_fractionalIdeal_smul_mem_lattice :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  let I : Submodule (𝓞 E) E := L.comap f
  have hI : ∀ s, s ∈ I ↔ s • x ∈ L := fun s => by simp [I, f]
  let π : (Fin n → E) →ₗ[𝓞 E] E := LinearMap.proj (R := 𝓞 E) (φ := fun _ => E) i
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (M := L)
  have hJ : IsFractional (𝓞 E)⁰ (L.map π) := FractionalIdeal.isFractional_of_fg (hfg.map π)
  let J : FractionalIdeal (𝓞 E)⁰ E := ⟨L.map π, hJ⟩
  have hle : I ≤ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ (x i)⁻¹ * J :
      FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    intro s hs
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    refine ⟨s * x i, ?_, ?_⟩
    · show s * x i ∈ L.map π
      exact ⟨s • x, (hI s).1 hs, by simp [π]⟩
    · field_simp
  exact ⟨⟨I, FractionalIdeal.isFractional_of_le hle⟩, fun s => hI s⟩

end GlobalTheory
