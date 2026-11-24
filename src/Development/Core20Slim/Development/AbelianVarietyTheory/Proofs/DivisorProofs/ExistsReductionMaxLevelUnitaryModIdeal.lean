module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateUnitVectorCongrUnimodular
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.LevelRed

open GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem mk_eq_iff (h𝔪 : 𝔪 ≠ ⊥) (r b : 𝓞 D.host.E) :
    Ideal.Quotient.mk 𝔪 r = Ideal.Quotient.mk 𝔪 b ↔
      inc D (r : D.host.E) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  have e : inc D (r : D.host.E) - inc D (b : D.host.E) = inc D ((r - b : 𝓞 D.host.E) : D.host.E) := by
    push_cast
    rw [map_sub]
  rw [Ideal.Quotient.eq, e]
  constructor
  · intro h
    simpa using gen_mem_hatId D 𝔪 h (one_mem (OhE D))
  · intro h
    obtain ⟨c, hc, e'⟩ := (FractionalIdeal.mem_coeIdeal _).1 (GlobalTheory.HeisTranslate.mem_of_inc_mem_hatId h𝔪 h)
    have : c = r - b := RingOfIntegers.coe_injective e'
    exact this ▸ hc

theorem exists_redHom (h𝔪 : 𝔪 ≠ ⊥) : ∃ red : OhE D →+* 𝓞 D.host.E ⧸ 𝔪, ∀ (x : OhE D) (b : 𝓞 D.host.E),
    red x = Ideal.Quotient.mk 𝔪 b ↔ (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  choose r hr using fun x : OhE D => exists_red D 𝔪 h𝔪 (x : AE D) x.2
  have key : ∀ (x : OhE D) (b : 𝓞 D.host.E), Ideal.Quotient.mk 𝔪 (r x) = Ideal.Quotient.mk 𝔪 b ↔
      (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
    intro x b
    rw [mk_eq_iff D 𝔪 h𝔪]
    constructor
    · intro h
      have := add_mem (hr x) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hr x)
      rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := fun x => Ideal.Quotient.mk 𝔪 (r x)
            map_one' := ?_
            map_mul' := fun x y => ?_
            map_zero' := ?_
            map_add' := fun x y => ?_ }, key⟩
  · rw [← map_one (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_mul, key]
    have := add_mem (mul_mem_hatId D 𝔪 y.2 (hr x))
      (mul_mem_hatId D 𝔪 (VacMove.inc_int D (r x)) (hr y))
    convert this using 1
    push_cast
    rw [map_mul]
    ring
  · rw [← map_zero (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_add (f := _), key]
    have := add_mem (hr x) (hr y)
    convert this using 1
    push_cast
    rw [map_add (f := _)]
    ring

def intMat (N : ℕ) : ↥(intG D N) →* Matrix (Fin N) (Fin N) (OhE D) where
  toFun k := Matrix.of fun i j =>
    ⟨(((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j, (((mem_intG _).1 k.2) i j).1⟩
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  map_mul' x y := by
    ext i j
    simp [Matrix.mul_apply]

theorem exists_levelRed : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  intro D 𝔪 h𝔪 N
  obtain ⟨red, hred⟩ := exists_redHom D 𝔪 h𝔪
  exact ⟨((red.mapMatrix (m := Fin N)).toMonoidHom.comp (intMat D N)).toHomUnits,
    fun k i j b => hred (intMat D N k i j) b⟩

end GlobalTheory.LevelRed

end
