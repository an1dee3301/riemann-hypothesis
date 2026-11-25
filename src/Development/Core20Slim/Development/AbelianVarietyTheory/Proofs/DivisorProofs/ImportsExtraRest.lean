module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Formalism.PairingDivisors.StatementH
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Lemmas
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Prime

@[expose] public section

namespace GlobalTheory.PrimeMembershipExistence

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, Nat.Prime p ∧
      (p : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal w := by

  have hP := w.isPrime
  have hn0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem := Ideal.absNorm_mem w.asIdeal
  rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod, Nat.cast_prod] at hmem
  obtain ⟨p, hp, hpm⟩ := hP.prod_mem_iff.1 hmem
  rw [Nat.support_factorization] at hp
  rw [Nat.cast_pow] at hpm
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, hP.mem_of_pow_mem _ hpm⟩

end GlobalTheory.PrimeMembershipExistence
