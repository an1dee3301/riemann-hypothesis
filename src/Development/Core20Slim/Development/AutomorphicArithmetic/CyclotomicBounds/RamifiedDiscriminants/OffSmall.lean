module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
public import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
public import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField Ideal Formalism.BasicNotions
open scoped Pointwise

namespace UpperTheory.Ram

variable {R : Ranks} (H : Host R)

theorem natCast_notMem_of_coprime {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {l n : ℕ} (hl : (l : A) ∈ I)
    (h : Nat.Coprime n l) : (n : A) ∉ I := by
  intro hn
  obtain ⟨x, y, e⟩ : IsCoprime (n : A) (l : A) := Nat.Coprime.cast h
  exact hI ((Ideal.eq_top_iff_one _).2 (e ▸ I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hl)))




theorem half_ne_bot : H.𝔟 ≠ ⊥ := by
  intro hb
  have h1 := H.𝔟_spec.1
  rw [hb, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem half_not_le (Q : Ideal (𝓞 H.E)) [hQ : Q.IsPrime] (h : ((H.QS * H.q : ℕ) : 𝓞 H.E) ∉ Q) : ¬ H.𝔟 ≤ Q := by
  intro hle
  refine h (H.der.diffSupport Q hQ ?_)
  rw [H.𝔟_spec.1]
  exact (Ideal.dvd_iff_le.2 hle).mul_right _




end UpperTheory.Ram
