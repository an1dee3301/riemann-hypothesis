module

public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem denom_bound_mul : ∀ (E κ ι : Type) [Field E] [NumberField E] [Fintype κ] [Fintype ι] (T : Matrix κ ι E), ∃ M : ℕ, 0 < M ∧ ∀ (L : ℕ) (x : ι → E), (∀ i, IsIntegral ℤ ((L : E) * x i)) → ∀ k, IsIntegral ℤ (((M * L : ℕ) : E) * ∑ i, T k i * x i) := by
  intro E κ ι _ _ _ _ T
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image (fun p : κ × ι => T p.1 p.2))
  refine ⟨y.natAbs ^ 2, by positivity, ?_⟩
  intro L x hx k
  have hT : ∀ i, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * T k i) := by
    intro i
    have h1 := hint (T k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
    have hy' : IsIntegral ℤ ((y : E)) := by
      have := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E y)); simpa using this
    have : ((y.natAbs ^ 2 : ℕ) : E) * T k i = (y : E) * (y • T k i) := by
      rw [zsmul_eq_mul]
      have : ((y.natAbs ^ 2 : ℕ) : E) = ((y ^ 2 : ℤ) : E) := by
        have hz : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
        rw [← hz, Int.cast_natCast]
      rw [this]; push_cast; ring
    rw [this]
    exact hy'.mul h1
  have heq : (((y.natAbs ^ 2 * L : ℕ) : E) * ∑ i, T k i * x i)
      = ∑ i, (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [heq]
  have := Subalgebra.sum_mem (integralClosure ℤ E) (t := Finset.univ)
    (f := fun i => (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i))
    (fun i _ => Subalgebra.mul_mem _ (hT i) (hx i))
  exact this

end GlobalTheory
