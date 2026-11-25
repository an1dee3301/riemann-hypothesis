module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Batteries.Logic
public import Formalism.LocalRingCardinality.DataTheta
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Prod.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock.CommDM
open GlobalTheory.CCRFock

private lemma unitAt_apply_eq_ite {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ)
    (w : W) (a : Ix P Q) (b : Ix R S) : unitAt j z w a b = if (w, (a, b)) = j then z else 0 := by
  obtain ⟨j1, j2, j3⟩ := j
  by_cases h1 : w = j1
  · subst h1
    by_cases h2 : a = j2
    · subst h2
      by_cases h3 : b = j3
      · subst h3
        simp [unitAt]
      · simp [unitAt, h3, Ne.symm h3]
    · simp [unitAt, h2, Ne.symm h2]
  · simp [unitAt, h1]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  have key : ∀ (w : W) (a : Ix P Q) (b : Ix R S), lineSign a b * unitAt j z w a b * star (unitAt k z' w a b) =
      if (w, (a, b)) = j then (if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0) else 0 := by
    intro w a b
    rw [unitAt_apply_eq_ite, unitAt_apply_eq_ite]
    by_cases hj : (w, (a, b)) = j
    · subst hj
      by_cases hk : (w, (a, b)) = k
      · subst hk
        simp
      · simp [hk]
    · simp [hj]
  simp only [key]
  rw [Fintype.sum_eq_single j.1, Fintype.sum_eq_single j.2.1, Fintype.sum_eq_single j.2.2]
  all_goals first
    | (intro x hx; simp [Prod.ext_iff, hx])
    | simp

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand {V : Type} [AddCommGroup V] [Module ℂ V] (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_smul, mul_add, add_mul, mul_sub, sub_mul,
    smul_add, smul_sub, smul_neg]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  rw [← mul_inv]
  congr 1
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  linear_combination 4 * h

theorem fockD_fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockD H j * GlobalTheory.CCRFock.fockM H k - GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockD H j =
      if j = k then 1 else 0 := by
  intro V _ _ W _ _ P Q R S H _ _ hcomm j k
  simp only [GlobalTheory.CCRFock.fockD, GlobalTheory.CCRFock.fockM]
  rw [comm_expand, hcomm, hcomm, hcomm, hcomm, sum_unitAt, sum_unitAt, sum_unitAt, sum_unitAt, inv_sq]
  by_cases hjk : j = k
  · subst hjk
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
  · simp [hjk]

end GlobalTheory.CCRFock.CommDM
