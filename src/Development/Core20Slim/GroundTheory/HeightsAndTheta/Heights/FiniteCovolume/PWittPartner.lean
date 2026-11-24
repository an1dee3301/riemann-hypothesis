module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem WittPartner.proof (h : HermitianForm F E W) : WittPartner.Statement h := by
  intro x₀ hx₀ hiso

  have hne : h.toSesq x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply h.nonsingular.1
    rw [h0, map_zero]
  obtain ⟨y', hy'⟩ : ∃ y', h.toSesq x₀ y' ≠ 0 := by
    by_contra hc
    exact hne (LinearMap.ext fun z => not_not.1 fun hz => hc ⟨z, hz⟩)

  obtain ⟨y, hy⟩ : ∃ y, h.toSesq x₀ y = 1 :=
    ⟨(h.toSesq x₀ y')⁻¹ • y', by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']⟩
  have hyx : h.toSesq y x₀ = 1 := by
    rw [← h.isSymm.eq x₀ y, hy, map_one]

  obtain ⟨a, ha_def⟩ : ∃ a, h.toSesq y y = a := ⟨_, rfl⟩
  have ha : conjHom F E a = a := by
    rw [← ha_def]
    exact h.isSymm.eq y y
  have ht : conjHom F E (a / 2) = a / 2 := by
    rw [map_div₀, ha, map_ofNat]

  have hl : ∀ z, h.toSesq (y - (a / 2) • x₀) z = h.toSesq y z - (a / 2) * h.toSesq x₀ z := by
    intro z
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, ht, smul_eq_mul]
  refine ⟨y - (a / 2) • x₀, ?_, ?_⟩
  · rw [map_sub, map_smul, hy, hiso, smul_zero, sub_zero]
  · rw [hl]
    simp only [map_sub, map_smul, smul_eq_mul, hyx, hy, hiso, ha_def]
    ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
