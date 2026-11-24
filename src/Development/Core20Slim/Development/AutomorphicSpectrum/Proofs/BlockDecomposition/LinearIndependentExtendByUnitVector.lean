module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree

variable {K : Type} [CommRing K] {M n : ℕ}

theorem sum_vec_zero (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) 0
      = g 0 * α + ∑ j : Fin n, g j.succ * c j := by
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [vec]

theorem sum_vec_succ (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K)
    (i : Fin M) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) i.succ
      = (∑ j : Fin n, g j.succ • X j) i := by
  rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_apply]
  simp [vec]

theorem linearIndependent_vec_iff (K : Type) [CommRing K] (M n : ℕ) (α : K) (hα : IsUnit α)
    (c : Fin n → K) (X : Fin n → Fin M → K) :
    LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h w hw j
    obtain ⟨β, hβ⟩ := hα.exists_left_inv
    have key := h (Fin.cons (-(∑ j : Fin n, w j * c j) * β) w) (by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [sum_vec_zero]
        simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]
        rw [mul_assoc, hβ]
        ring
      · rw [sum_vec_succ]
        simp only [Fin.cons_succ, Pi.zero_apply]
        rw [hw]
        rfl) j.succ
    simpa using key
  · intro h w hw
    have hs : ∀ j : Fin n, w j.succ = 0 := by
      refine h (fun j => w j.succ) ?_
      funext i
      have := congrFun hw i.succ
      rwa [sum_vec_succ] at this
    have h0 : w 0 = 0 := by
      have := congrFun hw 0
      rw [sum_vec_zero] at this
      simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
      exact (hα.mul_left_eq_zero).1 this
    intro a
    refine Fin.cases h0 hs a

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree
