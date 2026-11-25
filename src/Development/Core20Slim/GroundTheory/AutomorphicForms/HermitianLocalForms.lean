module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianBinaryValues
public import Development.Core20Slim.GroundTheory.AutomorphicForms.UnitaryGroupScheme
public import Batteries.Logic
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianNormLocal
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianOrthogonal
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

section QuadConj

variable {F : Type*} [Field F] (a : F)

end QuadConj

section Coordinates

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]

theorem exists_algEquiv_quadraticAlgebra (h2 : (2 : K) ≠ 0) :
    ∃ (d : K) (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0), (∀ r : K, r ^ 2 ≠ d) ∧
      ∀ x, ψ (conj K E x) = star (ψ x) := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := K) (E := E)
  set α := ζ - algebraMap K E (Algebra.trace K E ζ / 2) with hαdef
  have hα : α ∉ Set.range (algebraMap K E) := by
    rintro ⟨c, hc⟩
    apply hζ
    exact ⟨c + Algebra.trace K E ζ / 2, by rw [map_add (f := _), hc, hαdef]; ring⟩
  have htr : Algebra.trace K E α = 0 := by
    rw [hαdef, map_sub, trace_algebraMap_quadratic]
    field_simp
    ring
  have hconj : conj K E α = -α := by rw [conj_apply, htr, map_zero, zero_sub]
  set d := -Algebra.norm K α with hd
  have hαα : α * α = algebraMap K E d := by
    have := mul_conj (F := K) α
    rw [hconj] at this
    rw [hd, map_neg]
    linear_combination -this
  let f : QuadraticAlgebra K d 0 →ₐ[K] E :=
    QuadraticAlgebra.lift ⟨α, by rw [hαα, Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]⟩
  have hf : ∀ z : QuadraticAlgebra K d 0,
      f z = algebraMap K E z.re + algebraMap K E z.im * α := by
    intro z
    simp [f, Algebra.smul_def]
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    rw [hf] at hz
    by_cases him : z.im = 0
    · rw [him, map_zero, zero_mul, add_zero] at hz
      ext
      · exact (algebraMap K E).injective (by simp [hz])
      · simpa using him
    · exfalso
      apply hα
      refine ⟨-z.re / z.im, ?_⟩
      have him' : algebraMap K E z.im ≠ 0 := (map_ne_zero _).2 him
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hz
  have hbij : Function.Bijective f := by
    refine ⟨hinj, ?_⟩
    have := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by rw [QuadraticAlgebra.finrank_eq_two, Algebra.IsQuadraticExtension.finrank_eq_two])
    exact this.1 hinj
  refine ⟨d, (AlgEquiv.ofBijective f hbij).symm, ?_, ?_⟩
  · intro r hr
    apply hα
    have h0 : (α - algebraMap K E r) * (α + algebraMap K E r) = 0 := by
      rw [← hr, map_pow] at hαα
      linear_combination hαα
    rcases mul_eq_zero.1 h0 with h | h
    · exact ⟨r, by linear_combination -h⟩
    · exact ⟨-r, by rw [map_neg]; linear_combination -h⟩
  · intro x
    obtain ⟨z, rfl⟩ := hbij.2 x
    apply (AlgEquiv.ofBijective f hbij).injective
    rw [AlgEquiv.apply_symm_apply]
    change conj K E (f z) = f (star ((AlgEquiv.ofBijective f hbij).symm (f z)))
    have : (AlgEquiv.ofBijective f hbij).symm (f z) = z :=
      (AlgEquiv.ofBijective f hbij).symm_apply_apply z
    rw [this, hf, hf, map_add (f := _), map_mul, conj_algebraMap, conj_algebraMap, hconj,
      QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    simp

end Coordinates

section BaseChange

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
  {d : K} (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0) (R : Type*) [CommRing R] [Algebra K R]

def tensorQuadEquiv : R ⊗[K] E ≃ₐ[R] QuadraticAlgebra R (algebraMap K R d) 0 :=
  (Algebra.TensorProduct.congr AlgEquiv.refl ψ).trans (quadTensorEquiv d R)

omit [Algebra.IsQuadraticExtension K E] in
theorem tensorQuadEquiv_tmul (r : R) (x : E) :
    tensorQuadEquiv ψ R (r ⊗ₜ x) =
      ⟨r * algebraMap K R (ψ x).re, r * algebraMap K R (ψ x).im⟩ := by
  simp [tensorQuadEquiv, quadTensorEquiv_tmul]


variable {ψ} in
theorem tensorQuadEquiv_conjBase (hψ : ∀ x, ψ (conj K E x) = star (ψ x)) (z : R ⊗[K] E) :
    tensorQuadEquiv ψ R (conjBase K E R z) = star (tensorQuadEquiv ψ R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [conjBase_tmul, tensorQuadEquiv_tmul, tensorQuadEquiv_tmul, hψ]
    ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]

end BaseChange

section Congr

variable {A : Type*} [CommRing A] (s : A →+* A) {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {s}

end Congr

section Bridge

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Bridge

section LocalQuad

variable {F : Type*} [Field F] (d : F) {ι : Type*} [Fintype ι] [DecidableEq ι]

end LocalQuad

end GroundTheory.Automorphic
