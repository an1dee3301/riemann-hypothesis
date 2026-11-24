module

public import ReciprocityTheory.Chebotarev.EulerSum
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Mathlib
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.LatITopBasis
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.IdealBasis
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.NormArea
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem exists_latI_basis (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K))
    (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * Real.sqrt d / 2 := by
  obtain ⟨a₀, b₀, h₀, hl₀, hc₀⟩ := latI_top_basis K d hd4 x hx hK φ
  obtain ⟨a, b, h, hl, hc⟩ := latI_basis K hK φ a₀ b₀ h₀ hl₀ 𝔞 h𝔞
  exact ⟨a, b, h, hl, by rw [hc, hc₀]; ring⟩

theorem discr_latI_ne_zero (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    discr (latI φ 𝔞 1) ≠ 0 := by
  obtain ⟨a, b, h, hl, -⟩ := exists_latI_basis K d hd4 x hx hK φ 𝔞 h𝔞
  rw [hl]; exact discr_closure_pair_ne_zero a b h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
