module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem invDifferent_exists_max_valuation :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧
      (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
      ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
        w.valuation E f ≤ w.valuation E e := by
  intro E _ _ w
  classical

  have hint : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      IsIntegral ℤ ((NumberField.discr E : E) * f) := by
    intro f hf
    have hmem : f ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
      have h := hf y
      rw [IsIntegrallyClosed.isIntegral_iff] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply, hk, mul_comm]
    have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
      (1 : Submodule (𝓞 E) E) hb h1 hmem
    rw [← coe_discr, Algebra.smul_def, mul_one] at this
    simpa using this
  have hle : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      w.valuation E ((NumberField.discr E : E) * f) ≤ 1 := by
    intro f hf
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hint f hf)
    rw [← hy]
    exact w.valuation_le_one y
  have hd0 : (NumberField.discr E : E) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hvd : w.valuation E (NumberField.discr E : E) ≠ 0 := by simpa using hd0
  have hP1 : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * 1)) := fun o => by
    rw [mul_one]; exact Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
  let S : ℤ → Prop := fun k => ∃ f : E, f ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) ∧
      WithZero.log (w.valuation E f) = k
  have hbdd : ∃ b, ∀ z, S z → z ≤ b := by
    refine ⟨-WithZero.log (w.valuation E (NumberField.discr E : E)), ?_⟩
    rintro z ⟨f, hf0, hf, rfl⟩
    have hvf : w.valuation E f ≠ 0 := by simpa using hf0
    have h := hle f hf
    rw [map_mul, ← WithZero.exp_log hvd, ← WithZero.exp_log hvf, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hne : ∃ z, S z := ⟨_, 1, one_ne_zero, hP1, rfl⟩
  obtain ⟨k, ⟨e, he0, he, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨e, he0, he, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hvf : w.valuation E f ≠ 0 := by simpa using hf0
  have hve : w.valuation E e ≠ 0 := by simpa using he0
  have h := hmax _ ⟨f, hf0, hf, rfl⟩
  rw [← WithZero.exp_log hvf, ← WithZero.exp_log hve, WithZero.exp_le_exp]
  exact h

end GlobalTheory
