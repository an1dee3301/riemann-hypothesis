module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.L2.Th1.A (shortW logSer expSer wpReg xS xPlus)
open Formalism.L2.Th1.C (HasSecondLogDeriv wpShift IsEndoZ IsEndoCurve wTr)

namespace CurveNormEndomorphisms

section Alg

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem map_derivative (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.derivative (R := K) f) =
      PowerSeries.derivative (R := K') (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_derivative]

theorem map_rescale (a : K) (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.rescale a f) =
      PowerSeries.rescale (φ a) (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_rescale]

theorem map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (wpShift e c) = wpShift (PowerSeries.map φ e) (φ c) := by
  unfold wpShift
  simp

theorem second_log_derivative_map {f g : PowerSeries K} (h : HasSecondLogDeriv f g) :
    HasSecondLogDeriv (PowerSeries.map φ f) (PowerSeries.map φ g) := by
  unfold HasSecondLogDeriv at h ⊢
  have := congrArg (PowerSeries.map φ) h
  simpa [map_derivative] using this

theorem second_log_derivative_unique {f g g' : PowerSeries K} (hf : PowerSeries.constantCoeff f = 1)
    (h : HasSecondLogDeriv f g) (h' : HasSecondLogDeriv f g') : g = g' := by
  unfold HasSecondLogDeriv at h h'
  have hf0 : f ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h0
    rw [h0, map_zero] at hf
    exact zero_ne_one hf
  exact mul_right_cancel₀ hf0 (h.symm.trans h')

theorem cc_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.constantCoeff (wpShift e c) = 1 := by
  unfold wpShift
  simp

theorem isEndoZ_map {e : PowerSeries K} {ι : Type} [Fintype ι] {neg : ι → ι} {c : ι → K}
    {w : ι → PowerSeries K} {al : K} (h : IsEndoZ e neg c w al) :
    IsEndoZ (PowerSeries.map φ e) neg (fun P => φ (c P)) (fun P => PowerSeries.map φ (w P))
      (φ al) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun P => ?_, ?_⟩
  · have := second_log_derivative_map φ (h2 P)
    simp only [map_sub, map_mul, map_ofNat, map_wpShift] at this
    exact this
  · have := congrArg (PowerSeries.map φ) h3
    simpa [map_rescale] using this

theorem endoCurve_of_endoZ [CharZero K] [CharZero K'] (W : WeierstrassCurve K) {ι : Type}
    [Fintype ι] {neg : ι → ι} {xP yP : ι → K} {al : K} {wF : ι → PowerSeries K'}
    (hEq : ∀ P, W.toAffine.Equation (xP P) (yP P))
    (hneg : ∀ P, xP (neg P) = xP P ∧ yP (neg P) = W.toAffine.negY (xP P) (yP P))
    (h : IsEndoZ (PowerSeries.map φ (wpReg W)) neg (fun P => φ (xP P + W.b₂ / 12)) wF (φ al)) :
    IsEndoCurve W neg xP yP al := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hEq, h1, hneg, ?_⟩
  have key : ∀ P, PowerSeries.map φ (wTr W (xP P) (yP P)) +
      PowerSeries.map φ (wTr W (xP (neg P)) (yP (neg P))) = wF P + wF (neg P) := by
    intro P
    have hc := second_log_derivative_map φ (Formalism.L2.Th1.C.curve_second_log_derivative K W (xP P) (yP P) (hEq P))
    rw [map_wpShift, ← (hneg P).2] at hc
    have hx : wTr W (xP P) (yP (neg P)) = wTr W (xP (neg P)) (yP (neg P)) := by
      rw [(hneg P).1]
    rw [hx] at hc
    have hu := second_log_derivative_unique (cc_wpShift _ _) hc (h2 P)
    simp only [map_sub, map_mul, map_ofNat] at hu
    linear_combination -hu
  have hinv : Function.Involutive neg := h1
  have hs1 : ∑ P, PowerSeries.map φ (wTr W (xP (neg P)) (yP (neg P))) =
      ∑ P, PowerSeries.map φ (wTr W (xP P) (yP P)) :=
    Equiv.sum_comp hinv.toPerm (fun P => PowerSeries.map φ (wTr W (xP P) (yP P)))
  have hs2 : ∑ P, wF (neg P) = ∑ P, wF P := Equiv.sum_comp hinv.toPerm wF
  have hsum : ∑ P, PowerSeries.map φ (wTr W (xP P) (yP P)) = ∑ P, wF P := by
    have h4 := Finset.sum_congr (rfl : (Finset.univ : Finset ι) = Finset.univ) (fun P _ => key P)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs1, hs2] at h4
    have h2' : (2 : PowerSeries K') ≠ 0 := by
      intro h0
      have h5 := congrArg PowerSeries.constantCoeff h0
      rw [map_ofNat, map_zero] at h5
      exact two_ne_zero h5
    apply mul_left_cancel₀ h2'
    linear_combination h4
  apply PowerSeries.map_injective φ φ.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, PowerSeries.map_C, map_pow, map_rescale, h3, map_add (f := _), map_sum]
  simp only [map_sub, PowerSeries.map_C, Finset.sum_sub_distrib]
  rw [hsum]

end Alg

theorem omega_sq (d : ℕ) : omegaK d ^ 2 = omegaK d - (1 + (d : ℂ)) / 4 := by
  have h : (((Real.sqrt d : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  unfold omegaK
  linear_combination (Complex.I ^ 2 / 4) * h + ((d : ℂ) / 4) * Complex.I_sq

theorem mul_bar (d : ℕ) (m n : ℂ) :
    (m + n * omegaK d) * (m + n * (1 - omegaK d)) = m ^ 2 + m * n + n ^ 2 * ((1 + (d : ℂ)) / 4) := by
  linear_combination (-n ^ 2) * omega_sq d

theorem normInt_cast {dK : ℕ} (hmod : dK % 4 = 3) (m n : ℤ) :
    ((normInt dK m n : ℤ) : ℝ) =
      (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (dK : ℝ)) / 4) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hdiv : ((dK : ℤ) + 1) / 4 = k := by omega
  have hr : (dK : ℝ) + 1 = 4 * (k : ℝ) := by exact_mod_cast hk
  unfold normInt
  rw [hdiv]
  push_cast
  have : (1 + (dK : ℝ)) / 4 = (k : ℝ) := by linarith
  rw [this]

theorem cdata {dK : ℕ} (L : PeriodPair) (hmod : dK % 4 = 3) (hCM : Formalism.L2.Th1.CM.HasCMBy dK L)
    (m n : ℤ) (hN : normInt dK m n ≠ 0) :
    ∃ (S : Finset ℂ) (neg : S → S), ((S.card : ℤ) + 1 = normInt dK m n) ∧
      (∀ P : S, ((S.card + 1 : ℕ) : ℂ) * (P : ℂ) ∈ L.lattice ∧ (P : ℂ) ∉ L.lattice) ∧
      (∀ P : S, L.weierstrassP (neg P : ℂ) = L.weierstrassP (P : ℂ) ∧
        L.derivWeierstrassP (neg P : ℂ) = -L.derivWeierstrassP (P : ℂ)) ∧
      IsEndoZ (Formalism.L2.Th1.F.pSeries L) neg (fun P : S => L.weierstrassP (P : ℂ))
        (fun P : S => Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))
        ((m : ℂ) + (n : ℂ) * omegaK dK) ∧
      ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) = (S.card : ℂ) + 1 ∧
      ((m : ℂ) + (n : ℂ) * omegaK dK) *
          (((m : ℂ) + (n : ℂ) * omegaK dK) - ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))) *
          Formalism.L2.Th1.F.s2 L = ∑ P : S, L.weierstrassP (P : ℂ) := by
  have hmn : (m, n) ≠ (0, 0) := by
    intro h
    rw [Prod.mk.injEq] at h
    apply hN
    rw [h.1, h.2]
    simp [normInt]
  have hd : 0 < dK := by omega
  obtain ⟨S, hS, hcard, -, hs2⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hCM m n hmn hd
  obtain ⟨hst, hnorm⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hCM m n
  have hprod : ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (S.card : ℂ) + 1 := by
    rw [mul_bar]
    have := congrArg (fun x : ℝ => (x : ℂ)) hcard
    push_cast at this
    rw [this]
  have ha0 : (m : ℂ) + (n : ℂ) * omegaK dK ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    have h1 : ((S.card + 1 : ℕ) : ℂ) = 0 := by push_cast; exact hprod.symm
    exact (Nat.succ_ne_zero _) (Nat.cast_eq_zero.mp h1)
  obtain ⟨neg, hneg, hE⟩ := Formalism.L2.Th1.F.endoZInstance L _ S ha0 hst hS
  refine ⟨S, neg, ?_, ?_, ?_, hE, hprod, ?_⟩
  · have : (((S.card : ℤ) + 1 : ℤ) : ℝ) = ((normInt dK m n : ℤ) : ℝ) := by
      rw [normInt_cast hmod, ← hcard]
      push_cast
      ring
    exact_mod_cast this
  · intro P
    refine ⟨?_, (hS.1 P P.2).2⟩
    have hbar := (Formalism.L2.Th1.F.hasCMByStable dK L hCM (m + n) (-n)).1
    have h1 := hbar _ (hS.1 P P.2).1
    have e : ((S.card + 1 : ℕ) : ℂ) * (P : ℂ) =
        (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK) *
          (((m : ℂ) + (n : ℂ) * omegaK dK) * (P : ℂ)) := by
      push_cast
      rw [← hprod]
      ring
    rw [e]
    exact h1
  · intro P
    have e : (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ) := by
      simp
    constructor
    · rw [e, L.weierstrassP_add_coe, L.weierstrassP_neg]
    · rw [e, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]
  · rw [Finset.sum_coe_sort S (fun P => L.weierstrassP P), ← hs2, hnorm]
    have := mul_bar dK (m : ℂ) (n : ℂ)
    push_cast
    linear_combination (-Formalism.L2.Th1.F.s2 L) * this






end CurveNormEndomorphisms


end Formalism.L2.Th1.D
