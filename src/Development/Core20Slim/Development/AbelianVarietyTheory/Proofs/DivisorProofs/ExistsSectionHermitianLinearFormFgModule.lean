module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.FractionalIdeal.Operations

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.FormSection

theorem exists_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    ∀ x : Fin n → E, (∃ z ∈ L, form σ J z x ≠ 0) →
    ∃ y₀ : Fin n → E, form σ J y₀ x = 1 ∧ ∀ z ∈ L, form σ J z x • y₀ ∈ L := by
  intro F E _ _ _ _ _ σ n J L hL x ⟨z₀, hz₀L, hz₀⟩
  classical

  let φ : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun a z => by
        simp only [form, RingHom.id_apply]
        rw [← algebraMap_smul E a z, smul_dotProduct, smul_eq_mul, Algebra.smul_def] }
  have hφ : ∀ z, φ z = form σ J z x := fun _ => rfl
  have hφE : ∀ (c : E) z, form σ J (c • z) x = c * form σ J z x := by
    intro c z; simp [form, smul_dotProduct]
  let I : Submodule (𝓞 E) E := L.map φ
  have hIfg : I.FG := hL.map φ
  let I' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hIfg⟩
  have hmemI : ∀ z ∈ L, form σ J z x ∈ I' := fun z hz => ⟨z, hz, rfl⟩
  have hI0 : I' ≠ 0 := by
    intro h
    have := hmemI z₀ hz₀L
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact hz₀ this
  have hone : I' * I'⁻¹ = 1 := mul_inv_cancel₀ hI0
  let S : Submodule (𝓞 E) E :=
    { carrier := {e | ∃ y₀ : Fin n → E, form σ J y₀ x = e ∧ ∀ c ∈ I, c • y₀ ∈ L}
      add_mem' := by
        rintro _ _ ⟨y₁, rfl, h₁⟩ ⟨y₂, rfl, h₂⟩
        refine ⟨y₁ + y₂, by simp [form, add_dotProduct], fun c hc => ?_⟩
        rw [smul_add]; exact L.add_mem (h₁ c hc) (h₂ c hc)
      zero_mem' := ⟨0, by simp [form], fun c _ => by simp⟩
      smul_mem' := by
        rintro a _ ⟨y, rfl, h⟩
        refine ⟨a • y, ?_, fun c hc => ?_⟩
        · rw [← hφ, ← hφ, map_smul]
        · rw [smul_comm]; exact L.smul_mem a (h c hc) }
  have hle : I * ((I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ S := by
    refine Submodule.mul_le.mpr fun i hi j hj => ?_
    obtain ⟨z, hz, rfl⟩ := hi
    refine ⟨j • z, ?_, fun c hc => ?_⟩
    · rw [hφE, hφ, mul_comm]
    · have hcj : j * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        (FractionalIdeal.mem_inv_iff hI0).mp hj c hc
      obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hcj
      rw [smul_smul, mul_comm, ← ha, algebraMap_smul]
      exact L.smul_mem a hz
  have h1 : (1 : E) ∈ S := by
    apply hle
    have : (1 : E) ∈ ((I' * I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [hone]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
    rwa [FractionalIdeal.coe_mul] at this
  obtain ⟨y₀, hy₀, hL'⟩ := h1
  exact ⟨y₀, hy₀, fun z hz => hL' _ (hmemI z hz)⟩

end GlobalTheory.FormSection
