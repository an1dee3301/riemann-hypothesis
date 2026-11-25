module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualLatticeMultiple
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

theorem inverseDifferent_multiple (E : Type*) [Field E] [NumberField E] :
    ∃ δ : ℤ, δ ≠ 0 ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z) := by
  classical
  set b := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  obtain ⟨δ, hδ, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image bd)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hsum := bd.sum_repr z
  have key : (δ : E) * z = ∑ i, (bd.repr z i) • ((δ : E) * bd i) := by
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def]; ring
  rw [key]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨n, hn⟩ := hz (RingOfIntegers.basis E i)
  have hr : bd.repr z i = (n : ℚ) := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, integralBasis_apply,
      mul_comm, hn]
  rw [hr, show ((n : ℚ) • ((δ : E) * bd i)) = (n : ℤ) • ((δ : E) * bd i) by
    rw [← Int.cast_smul_eq_zsmul ℚ]]
  refine IsIntegral.smul _ ?_
  have := hint (bd i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rwa [zsmul_eq_mul] at this

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem DualLatticeMultiple.proof (h : HermitianForm F E W) : DualLatticeMultiple.Statement h := by
  intro D
  obtain ⟨δ, hδ, hdiff⟩ := inverseDifferent_multiple E
  refine ⟨δ * (D.factorial : ℤ), mul_ne_zero hδ (by exact_mod_cast D.factorial_ne_zero),
    fun La hLa => ⟨fun x hx y hy => ?_, fun y hy => ?_⟩⟩
  · have hi : IsIntegral ℤ (Algebra.trace ℚ E (h.toSesq x y)) :=
      Algebra.isIntegral_trace ((mem_integralClosure_iff ℤ E).mp (hLa.integral x hx y hy))
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨n, by rw [← hn]; simp⟩
  ·
    have hdual : δ • y ∈ dualLattice h La := by
      intro x hx
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
      refine (mem_integralClosure_iff ℤ E).mpr (hdiff _ fun a => ?_)
      obtain ⟨n, hn⟩ := hy _ (hLa.isLattice.smul_mem a x hx)
      exact ⟨n, by rw [← hn, LinearMap.map_smul, smul_eq_mul]⟩

    have hm := AddSubgroup.nsmul_relIndex_mem La hdual
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
    have : (D.factorial : ℤ) • (δ • y) ∈ La := by
      rw [hc, natCast_zsmul, mul_comm, mul_nsmul]
      rw [smul_comm]
      exact AddSubgroup.nsmul_mem _ hm _
    rwa [smul_smul, mul_comm] at this

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
