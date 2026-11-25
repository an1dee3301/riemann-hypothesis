module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.NormSum.VacInt.PartFin

open GlobalTheory.NormSum.VacInt

section Cut

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem cutM_of_eq_zero (e : R) (he : e * e = e) (h : e = 0) (A : Matrix n n R) : cutM e he A = 1 := by
  subst h
  show (0 : R) • A + (1 - 0 : R) • (1 : Matrix n n R) = 1
  simp

theorem cutM_add (e e' f : R) (he : e * e = e) (he' : e' * e' = e') (hf : f * f = f) (h0 : e * e' = 0)
    (h : f = e + e') (A : Matrix n n R) : cutM f hf A = cutM e he A * cutM e' he' A := by
  subst h
  have h1 : e * (1 - e') = e := by linear_combination - h0
  have h2 : (1 - e) * e' = e' := by linear_combination - h0
  have h3 : (1 - e) * (1 - e') = 1 - (e + e') := by linear_combination h0
  show (e + e') • A + (1 - (e + e')) • (1 : Matrix n n R) =
    (e • A + (1 - e) • (1 : Matrix n n R)) * (e' • A + (1 - e') • (1 : Matrix n n R))
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, h0, h1, h2, h3,
    zero_smul, zero_add, add_smul]
  abel

end Cut

variable {E : Type} [Field E] [NumberField E]

theorem eps_empty : eps E (fun p => p ∈ (∅ : Finset ℕ)) = 0 :=
  ext_prV fun v => by rw [prV_eps, map_zero]; simp

theorem eps_insert (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p ∈ insert q s) = eps E (fun p => p = q) + eps E (fun p => p ∈ s) :=
  ext_prV fun v => by
    rw [map_add (f := _), prV_eps, prV_eps, prV_eps]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · by_cases h2 : pr v ∈ s <;> simp [h1, h2]

theorem eps_single_mul (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p = q) * eps E (fun p => p ∈ s) = 0 :=
  ext_prV fun v => by
    rw [map_mul, prV_eps, prV_eps, map_zero]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · simp [h1]

theorem part_finset : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  intro D N y
  exact ⟨Subtype.ext (Units.ext (cutM_of_eq_zero _ _ eps_empty _)), fun q s h =>
    Subtype.ext (Units.ext (cutM_add _ _ _ _ _ _ (eps_single_mul q s h) (eps_insert q s h) _))⟩

end GlobalTheory.NormSum.VacInt.PartFin
