module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem fockM_comm_sum {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w, a, b⟩ := j
  obtain ⟨w', a', b'⟩ := k
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · by_cases hw : w = w'
    · subst hw
      by_cases ha : a = a'
      · subst ha
        by_cases hb : b = b'
        · subst hb; simp [unitAt]
        · simp [unitAt, hb, Ne.symm hb]
      · simp [unitAt, ha, Ne.symm ha]
    · simp [unitAt, hw]
  · intro c _ hc; simp [unitAt, Ne.symm hc]
  · simp
  · intro c _ hc; simp [unitAt, Ne.symm hc]
  · simp
  · intro c _ hc; simp [unitAt, hc]
  · simp

theorem fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockM H j * GlobalTheory.CCRFock.fockM H k = GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockM H j := by
  intro V _ _ W _ _ P Q R S H _ _ hc j k
  have h11 := hc (unitAt j 1) (unitAt k 1)
  have h1i := hc (unitAt j 1) (unitAt k Complex.I)
  have hi1 := hc (unitAt j Complex.I) (unitAt k 1)
  have hii := hc (unitAt j Complex.I) (unitAt k Complex.I)
  rw [fockM_comm_sum] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold fockM
    have c : Commute (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))
        (H (unitAt k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAt k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

end GlobalTheory.CCRFock
