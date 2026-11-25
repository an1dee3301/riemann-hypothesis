module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.PassageScaleFree
public import Formalism.QuotientMetricDivisors.FinalW
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMatrixMetricMeans
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.PairingDivisors.StatementH
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Module NumberField IsDedekindDomain
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.InfinitePlacesProbe

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def ClauseB (S : IndefData Df) (O : FunData K Df) (C b : ℝ) : Prop :=
  ∃ g : InfinitePlace K → ℝ, (∀ v p, Df.Qp Bs.μ0 p ≠ ⊥ → g v ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) ∧
    -(3 * C * O.f * O.m * (O.N : ℝ) ^ 2 * Real.log b) ≤ meanInf K g

theorem clauseB_of_lifts [_root_.NumberField.IsTotallyComplex K] {Df' : DefSide Bs} (S : IndefData Df) (S' : IndefData Df') (N : IndefNum Bs)
    (O : FunData K Df) {C b : ℝ} (hC : 0 ≤ C) (hb : 1 ≤ b) (hl : LevelLink S S') (h6 : S'.L6 N)
    (hm : Fintype.card Bs.J ≤ O.m) (hN : ∀ j, -(3 * C * O.f * (O.N : ℝ) ^ 2 * Real.log b) ≤ N.l6 j) :
    ClauseB S O C b := by
  refine ⟨fun _ => _, fun v p _ => ?_, (GlobalTheory.Proof.DualMatrixMetricMeans.meanInf_const _).ge⟩
  have h1 := Real.log_nonneg hb
  have h2 : ∑ _j : Bs.J, -(3 * C * O.f * (O.N : ℝ) ^ 2 * Real.log b) ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v) :=
    Finset.sum_le_sum fun j _ => (hN j).trans (by rw [hl.2.2]; exact h6 j p v)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have h3 : (Fintype.card Bs.J : ℝ) ≤ O.m := by exact_mod_cast hm
  have h4 : 0 ≤ 3 * C * O.f * (O.N : ℝ) ^ 2 * Real.log b := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 h4]

end GlobalTheory.InfinitePlacesProbe
