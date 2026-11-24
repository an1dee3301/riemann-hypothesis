module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StRationalUnipotent
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicCovolumeFinite
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Init.Core
public import Init.Data.Cast
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
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace RationalUnipotent

def unipMap (h : HermitianForm F E W) (x₀ y : W) (c : E) : W →ₗ[E] W where
  toFun x := x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y
  map_add' a b := by
    simp only [map_add (f := _)]
    module
  map_smul' r a := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    module

omit [NumberField E] in
theorem unipMap_apply (h : HermitianForm F E W) (x₀ y : W) (c : E) (x : W) :
    unipMap h x₀ y c x = x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y := rfl


omit [NumberField E] in
theorem sesq_swap (h : HermitianForm F E W) (u v : W) :
    h.toSesq u v = conj F E (h.toSesq v u) :=
  (h.isSymm.eq v u).symm


omit [NumberField E] in
theorem sesq_smul_left (h : HermitianForm F E W) (r : E) (u v : W) :
    h.toSesq (r • u) v = conj F E r * h.toSesq u v := by
  rw [LinearMap.map_smulₛₗ₂]
  rfl

theorem unipMap_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipMap h x₀ y c (unipMap h x₀ (-y) (conj F E c) x) = x := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add (f := _), map_smul, map_neg, LinearMap.neg_apply, hx₀, hy, hy']
  have key : h.toSesq x₀ x * conj F E c - -h.toSesq y x +
      (h.toSesq x₀ x * c - (h.toSesq y x + -(h.toSesq x₀ x * h.toSesq y y))) = 0 := by
    linear_combination h.toSesq x₀ x * hc
  linear_combination (norm := module) key • x₀

theorem sesq_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x x' : W) :
    h.toSesq (unipMap h x₀ y c x) (unipMap h x₀ y c x') = h.toSesq x x' := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add (f := _), map_smul, smul_eq_mul, LinearMap.add_apply,
    sesq_smul_left, hx₀, hy, hy', map_sub, map_mul, mul_zero, add_zero]
  rw [sesq_swap h x x₀, sesq_swap h x y]
  linear_combination conj F E (h.toSesq x₀ x) * h.toSesq x₀ x' * hc

def unipElem (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) : h.unitaryGroup :=
  ⟨LinearEquiv.ofLinearMap (unipMap h x₀ y c) (unipMap h x₀ (-y) (conj F E c))
    (LinearMap.ext fun x => unipMap_unipMap h hx₀ hy hc x)
    (LinearMap.ext fun x => by
      have e := unipMap_unipMap h (y := -y) (c := conj F E c) hx₀
        (by rw [map_neg, hy, neg_zero])
        (by rw [conj_conj, add_comm, hc, map_neg, LinearMap.map_neg₂, neg_neg]) x
      rwa [neg_neg, conj_conj] at e),
    fun x x' => sesq_unipMap h hx₀ hy hc x x'⟩

theorem unipElem_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipElem h hx₀ hy hc • x = unipMap h x₀ y c x := rfl

theorem unipElem_inv_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    (unipElem h hx₀ hy hc)⁻¹ • x = unipMap h x₀ (-y) (conj F E c) x := rfl

theorem unipMap_mem (h : HermitianForm F E W) {La : AddSubgroup W}
    (hsm : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) (hint : IsIntegralOn h La)
    {x₀ y : W} {c : E} (hx₀ : x₀ ∈ La) (hy : y ∈ La) (hc : c ∈ integralClosure ℤ E)
    {x : W} (hx : x ∈ La) : unipMap h x₀ y c x ∈ La := by
  have smul_mem : ∀ {α : E} {v : W}, α ∈ integralClosure ℤ E → v ∈ La → α • v ∈ La :=
    fun {α} {v} hα hv => hsm ⟨α, hα⟩ v hv
  rw [unipMap_apply]
  refine add_mem (add_mem hx (smul_mem ?_ hx₀)) (smul_mem (hint x₀ hx₀ x hx) hy)
  exact sub_mem (mul_mem (hint x₀ hx₀ x hx) hc) (hint y hy x hx)


omit [NumberField E] in
theorem conj_mem_integralClosure {c : E} (hc : c ∈ integralClosure ℤ E) :
    conj F E c ∈ integralClosure ℤ E :=
  (mem_integralClosure_iff ℤ E).2
    (((mem_integralClosure_iff ℤ E).1 hc).map (conj F E).toAlgHom.toRingHom.toIntAlgHom)

end RationalUnipotent


open RationalUnipotent in
theorem RationalUnipotent.proof (h : HermitianForm F E W) : RationalUnipotent.Statement h := by
  intro D La x₀ w₀ hD hx₀ hp
  refine ⟨1, one_pos, ?_⟩
  rintro y c hyW ⟨z₁, hz₁, rfl⟩ ⟨a, rfl⟩ hc
  simp only [Nat.cast_one, one_mul, one_smul] at hyW hc ⊢
  obtain ⟨hxx, hww, hxw⟩ := hp
  have hyx : h.toSesq x₀ z₁ = 0 := (mem_hypComplement.1 hyW).1
  have hyw : h.toSesq w₀ z₁ = 0 := (mem_hypComplement.1 hyW).2
  have hzx : h.toSesq z₁ x₀ = 0 := by rw [sesq_swap, hyx, map_zero]
  have hzw : h.toSesq z₁ w₀ = 0 := by rw [sesq_swap, hyw, map_zero]
  have haI : (a : E) ∈ integralClosure ℤ E :=
    (mem_integralClosure_iff ℤ E).2 (RingOfIntegers.isIntegral_coe a)
  set γ := unipElem h hxx hyx hc with hγ
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists v γ La).1 hv
      rw [hγ, unipElem_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ hz₁ haI hu
    · intro hv
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      rw [hγ, unipElem_inv_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ (neg_mem hz₁)
        (conj_mem_integralClosure haI) hv
  · rw [hγ, unipElem_smul, unipMap_apply, hxx, hzx]
    simp
  · rw [hγ, unipElem_smul, unipMap_apply, hxw, hzw]
    simp only [one_mul, sub_zero, one_smul]
    abel
  · intro z hz
    rw [hγ, unipElem_smul, unipMap_apply, (mem_hypComplement.1 hz).1]
    simp only [zero_mul, zero_sub, zero_smul, add_zero, neg_smul]
    abel

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
