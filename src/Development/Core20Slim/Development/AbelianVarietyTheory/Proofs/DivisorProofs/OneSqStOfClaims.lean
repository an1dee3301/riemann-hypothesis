module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCompLeSumOfInjOn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRatios
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.StepRatioAbsVwProd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
public import Formalism.PairingDivisors.StatementH
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
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
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw)

noncomputable section

namespace GlobalTheory.SqTop.OneSqProof

theorem vw_ratio_le {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e p q e0 h0 : ℕ)
    (he : e0 + p = e + q) (hle : e0 ≤ h0) (rq ζ γ zA zA' : K) (tk : Fin (p + q) → K) (ρ : ℤ → K) (a n0 : ℤ → ℝ)
    (er dl B : ℝ)
    (heq : rq * ∏ k ∈ range q, ρ ((e : ℤ) + k + 1) = ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k))
    (hρ0 : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ (h0 : ℤ) + p + q → ρ s ≠ 0)
    (hζ : ζ ≠ 0 ∧ vw w ζ = 0) (ht : ∀ k, tk k ≠ 0 ∧ |(vw w (tk k) : ℝ)| ≤ B) (hγ : γ ≠ 0) (hzA : zA ≠ 0)
    (hγv : (vw w γ : ℝ) ≤ vw w (zA * ∏ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s) + vw w zA' + 6 * dl)
    (her : 0 ≤ er)
    (hs : ∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q →
      0 ≤ a s ∧ 0 ≤ n0 s ∧ (vw w (ρ s) : ℝ) ≤ a s + er ∧ -(vw w (ρ s) : ℝ) ≤ a s + n0 s)
    (hsym : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) :
    rq ≠ 0 ∧ (vw w rq : ℝ) ≤ |(vw w zA : ℝ)| + |(vw w zA' : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) +
      ((2 * (h0 + p + q) : ℕ) : ℝ) * er + 6 * dl + ((p + q : ℕ) : ℝ) * B := by
  have hq0 : ∀ k ∈ range q, ρ ((e : ℤ) + k + 1) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hp0 : ∀ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hI0 : ∀ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s ≠ 0 := fun s hs => by
    rw [mem_Icc] at hs; exact hρ0 _ hs.1 (by omega)
  have hT : ∀ k ∈ (univ : Finset (Fin (p + q))), tk k ≠ 0 := fun k _ => (ht k).1
  have hPq := prod_ne_zero_iff.2 hq0
  have hPp := prod_ne_zero_iff.2 hp0
  have hPT := prod_ne_zero_iff.2 hT
  have hPI := prod_ne_zero_iff.2 hI0
  have hR : ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp
  have hrq : rq ≠ 0 := by
    rintro rfl; rw [zero_mul] at heq; exact hR heq.symm
  refine ⟨hrq, ?_⟩
  have hv := congrArg (vw w) heq
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hrq hPq, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hq0,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hζ.1 hPT) hγ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hζ.1 hPT,
    Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hT, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hp0, hζ.2] at hv
  have hz := Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hzA hPI
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hI0] at hz
  rw [hz] at hγv
  have hc := GlobalTheory.Square.count_factors e p q e0 h0 he hle (fun s => (vw w (ρ s) : ℝ)) a n0 er her
    (fun s h1 h2 => hs s h1 h2) (fun s h1 h2 => by simp only [hsym s h1 h2])
  have hvR : (vw w rq : ℝ) + ∑ k ∈ range q, (vw w (ρ ((e : ℤ) + k + 1)) : ℝ) =
      (∑ k, (vw w (tk k) : ℝ)) + vw w γ + ∑ k ∈ range p, (vw w (ρ ((e : ℤ) + q - k)) : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hv
    push_cast at this
    linarith
  have hTB : (∑ k, (vw w (tk k) : ℝ)) ≤ ((p + q : ℕ) : ℝ) * B := by
    calc (∑ k, (vw w (tk k) : ℝ)) ≤ ∑ _k : Fin (p + q), B :=
          sum_le_sum fun k _ => (le_abs_self _).trans (ht k).2
      _ = ((p + q : ℕ) : ℝ) * B := by simp
  have hIc : ((∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), vw w (ρ s) : ℤ) : ℝ) =
      ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ) := by push_cast; rfl
  have hγv' : (vw w γ : ℝ) ≤ vw w zA + (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ)) + vw w zA' + 6 * dl := by
    have := hγv; push_cast at this; linarith
  have a1 := le_abs_self (vw w zA : ℝ)
  have a2 := le_abs_self (vw w zA' : ℝ)
  linarith

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem wt_at {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ} {l : ℕ}
    (hS : ∀ l' ∈ S, l'.Prime) (hl : l.Prime) (hw : (l : 𝓞 K) ∈ w.asIdeal) (hc : l ∉ S → c l = 0) :
    Formalism.PairingDivisionLocalBalance.wt S c w = c l * (vw w (l : K) : ℝ) := by
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : l ∈ S
  · refine sum_eq_single_of_mem l h fun l' hl' hne => ?_
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp
  · rw [hc h, zero_mul]
    refine sum_eq_zero fun l' hl' => ?_
    have hne : l' ≠ l := fun e => h (e ▸ hl')
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp

theorem wt_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ}
    (hc : ∀ l ∈ S, 0 ≤ c l) : 0 ≤ Formalism.PairingDivisionLocalBalance.wt S c w :=
  sum_nonneg fun l hl => mul_nonneg (hc l hl) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w l)

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem exists_prime_mem' {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ w.asIdeal) (ringChar _))

end GlobalTheory.SqTop.OneSqProof

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop

namespace GlobalTheory.SqTop.OneSqProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SqTop.OneSqProof
