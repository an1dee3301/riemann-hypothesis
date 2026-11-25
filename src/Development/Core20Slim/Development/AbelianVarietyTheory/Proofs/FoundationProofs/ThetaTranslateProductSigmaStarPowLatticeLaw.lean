module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ThetaLaw

open GlobalTheory.ThetaParam

theorem pull_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  intro Λ hΛ t₀ ht y N hy ω hω z
  have hlaw : ∀ x ∈ Λ, ∀ v, sgStar Λ (v + x) = (if x / 2 ∈ Λ then 1 else -1) * sgStar Λ v *
      Complex.exp ((Real.pi : ℂ) * v * (starRingEnd ℂ) x / (area Λ : ℂ) +
        (Real.pi : ℂ) * x * (starRingEnd ℂ) x / (2 * (area Λ : ℂ))) := by
    intro x hx v
    have e := hΛ.sg_law hx v
    simp only [U1] at e
    rw [← e, mul_assoc, ← Complex.exp_add]
    ring_nf
    simp
  have hne : ∃ z, sgStar Λ z ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1
    rw [show sgStar Λ = fun _ => 0 from funext h] at hd
    simp at hd
  have hsl : ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
    fun ω hω z => hΛ.sg_law hω z
  have hx : (N : ℂ) * ω ∈ Λ := by simpa [nsmul_eq_mul] using nsmul_mem hω N
  have c1 : cocy Λ ((N : ℂ) * ω) y ^ 2 = 1 := by
    have e := cocy_pow Λ ω y N 1
    have r := cocy_root (m := 1) (n := N) hne hsl (by simpa using hω) hy
    simp only [Nat.cast_one, one_mul, mul_one] at e r
    rw [e, ← pow_mul, r]
  have c2 : cocy Λ ((N : ℂ) * ω) t₀ ^ 4 = 1 := by
    have r := cocy_root (m := 1) (n := 2) hne hsl (a := (N : ℂ) * ω) (b := t₀) (by simpa using hx) (by simpa using ht)
    simpa using r
  have hψ : ∀ x : ℂ, (if x / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro x; split_ifs <;> norm_num
  have hprod : ∀ v, U1 Λ y (GL3Theta.th0 Λ t₀) v * GL3Theta.th0 Λ t₀ v =
      sgStar Λ (v + y + t₀) * sgStar Λ (v + t₀) *
        (Complex.exp (-(Real.pi : ℂ) * (v + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) /
        (U1 Λ t₀ (sgStar Λ) 0) ^ 2 := by
    intro v
    simp only [GL3Theta.th0, U1]
    ring
  have hE : Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + y + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω) + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) =
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) *
      (cocy Λ ((N : ℂ) * ω) y ^ 2 * cocy Λ ((N : ℂ) * ω) t₀ ^ 4) := by
    simp only [cocy, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_add (f := _), map_natCast]
    push_cast
    ring
  rw [c1, c2, mul_one, mul_one] at hE
  rw [hprod, hprod,
    show (N : ℂ) * (z + ω) + y + t₀ = ((N : ℂ) * z + y + t₀) + (N : ℂ) * ω by ring,
    show (N : ℂ) * (z + ω) + t₀ = ((N : ℂ) * z + t₀) + (N : ℂ) * ω by ring,
    hlaw _ hx, hlaw _ hx, hlaw _ hω z, mul_pow, mul_pow, pow_mul (if ω / 2 ∈ Λ then (1 : ℂ) else -1) 2 (N ^ 2), hψ ω, one_pow, one_mul]
  linear_combination (sgStar Λ ((N : ℂ) * z + y + t₀) * sgStar Λ ((N : ℂ) * z + t₀) * sgStar Λ z ^ (2 * N ^ 2) /
      (U1 Λ t₀ (sgStar Λ) 0) ^ 2) * ((if (N : ℂ) * ω / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 * hE +
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) * hψ ((N : ℂ) * ω))

end GlobalTheory.ThetaLaw
