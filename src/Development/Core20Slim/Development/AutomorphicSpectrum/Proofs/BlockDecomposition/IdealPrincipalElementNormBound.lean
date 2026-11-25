module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink

theorem exists_ne_zero_mem_absNorm_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ →
      ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  intro E _ _
  refine ⟨(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      ((Module.finrank ℚ E).factorial : ℝ) / (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E *
      Real.sqrt |(discr E : ℝ)|, ?_, ?_⟩
  · have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
    have h1 : (0 : ℝ) < (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E :=
      pow_pos (div_pos (by norm_num) Real.pi_pos) _
    have h2 : (0 : ℝ) < ((Module.finrank ℚ E).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h3 : (0 : ℝ) < (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E :=
      pow_pos (Nat.cast_pos.mpr hn) _
    exact mul_pos (div_pos (mul_pos h1 h2) h3) (Real.sqrt_pos.mpr hd)
  · intro 𝔞 h𝔞
    have hmem : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    obtain ⟨a, ha, ha0, hle⟩ :=
      exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr E (Units.mk0 _ hmem)
    rw [Units.val_mk0] at ha
    obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    refine ⟨t, ht, ?_, ?_⟩
    · rintro rfl
      simp at ha0
    · have key : ((Ideal.absNorm (Ideal.span {t}) : ℚ)) =
          |Algebra.norm ℚ (algebraMap (𝓞 E) E t)| := by
        rw [← FractionalIdeal.coeIdeal_absNorm (K := E), FractionalIdeal.coeIdeal_span_singleton,
          FractionalIdeal.absNorm_span_singleton]
      have key' : (Ideal.absNorm (Ideal.span {t}) : ℝ) =
          ((|Algebra.norm ℚ (algebraMap (𝓞 E) E t)| : ℚ) : ℝ) := by
        rw [← key, Rat.cast_natCast]
      rw [key']
      refine hle.trans (le_of_eq ?_)
      simp only [Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink
