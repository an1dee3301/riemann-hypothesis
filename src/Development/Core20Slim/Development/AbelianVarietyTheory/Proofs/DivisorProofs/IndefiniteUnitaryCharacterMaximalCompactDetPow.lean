module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQContinuousCharacterEqDetPowProd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory.KChar

open Matrix

theorem norm_eq_one_of_compact {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] (f : G → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hc : Continuous f) (h1 : f 1 ≠ 0) : ∀ a, ‖f a‖ = 1 := by
  have hf1 : f 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    have h2 : f 1 * (f 1 - 1) = 0 := by rw [mul_sub, ← this]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h h1
    · exact sub_eq_zero.mp h
  obtain ⟨M, hM⟩ := (isCompact_range hc.norm).bddAbove
  have hb : ∀ a, ‖f a‖ ≤ M := fun a => hM ⟨a, rfl⟩
  have hpow : ∀ a (n : ℕ), f (a ^ n) = f a ^ n := by
    intro a n
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hle : ∀ a, ‖f a‖ ≤ 1 := by
    intro a
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have := hb (a ^ n)
    rw [hpow, norm_pow] at this
    linarith
  intro a
  have hinv : ‖f a‖ * ‖f a⁻¹‖ = 1 := by
    rw [← norm_mul, ← hmul, mul_inv_cancel, hf1, norm_one]
  have h2 := hle a⁻¹
  have h3 := hle a
  have h4 : 0 ≤ ‖f a‖ := norm_nonneg _
  have h5 : 0 ≤ ‖f a⁻¹‖ := norm_nonneg _
  nlinarith

theorem fromBlocks_mem (R S : ℕ) (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ)
    (ha : aᴴ * a = 1) (hd : dᴴ * d = 1) :
    (Matrix.fromBlocks a 0 0 d)ᴴ * Jm R S * Matrix.fromBlocks a 0 0 d = Jm R S := by
  change (Matrix.fromBlocks a 0 0 d)ᴴ * Matrix.fromBlocks 1 0 0 (-1) * Matrix.fromBlocks a 0 0 d =
    Matrix.fromBlocks 1 0 0 (-1)
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [ha, hd]

theorem unitary_ch {n : ℕ} (a : Matrix.unitaryGroup (Fin n) ℂ) : (a : Matrix (Fin n) (Fin n) ℂ)ᴴ * a = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp a.2
  simpa [Matrix.star_eq_conjTranspose] using this

theorem kchar : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∃ x y : ℤ, ∀ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      χ (Matrix.fromBlocks a 0 0 d) = a.det ^ x * d.det ^ y := by
  intro R S χ hmul hc hnz
  haveI := GlobalTheory.compactSpace_unitaryGroup (Fin R) ℂ
  haveI := GlobalTheory.compactSpace_unitaryGroup (Fin S) ℂ
  have h1R : (1 : Matrix (Fin R) (Fin R) ℂ)ᴴ * 1 = 1 := by simp
  have h1S : (1 : Matrix (Fin S) (Fin S) ℂ)ᴴ * 1 = 1 := by simp

  let fA : Matrix.unitaryGroup (Fin R) ℂ → ℂ := fun a => χ (Matrix.fromBlocks (a : Matrix (Fin R) (Fin R) ℂ) 0 0 1)
  have hmA : ∀ a b, fA (a * b) = fA a * fA b := by
    intro a b
    have e : Matrix.fromBlocks ((a * b : Matrix.unitaryGroup (Fin R) ℂ) : Matrix (Fin R) (Fin R) ℂ) 0 0
        (1 : Matrix (Fin S) (Fin S) ℂ) =
        Matrix.fromBlocks (a : Matrix (Fin R) (Fin R) ℂ) 0 0 1 * Matrix.fromBlocks (b : Matrix (Fin R) (Fin R) ℂ) 0 0 1 := by
      rw [Matrix.fromBlocks_multiply]; simp
    simp only [fA]
    rw [e]
    exact hmul _ _ (fromBlocks_mem R S _ _ (unitary_ch a) h1S) (fromBlocks_mem R S _ _ (unitary_ch b) h1S)
  have hcA : Continuous fA := by
    refine hc.comp_continuous ?_ (fun a => fromBlocks_mem R S _ _ (unitary_ch a) h1S)
    exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const continuous_const
  have hnA : ∀ a, ‖fA a‖ = 1 :=
    norm_eq_one_of_compact fA hmA hcA (hnz _ (fromBlocks_mem R S _ _ (unitary_ch 1) h1S))
  obtain ⟨x, hx⟩ := GlobalTheory.UpqChar.char_unitary fA hmA hnA hcA

  let fD : Matrix.unitaryGroup (Fin S) ℂ → ℂ := fun d => χ (Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0 (d : Matrix (Fin S) (Fin S) ℂ))
  have hmD : ∀ a b, fD (a * b) = fD a * fD b := by
    intro a b
    have e : Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0
        ((a * b : Matrix.unitaryGroup (Fin S) ℂ) : Matrix (Fin S) (Fin S) ℂ) =
        Matrix.fromBlocks 1 0 0 (a : Matrix (Fin S) (Fin S) ℂ) * Matrix.fromBlocks 1 0 0 (b : Matrix (Fin S) (Fin S) ℂ) := by
      rw [Matrix.fromBlocks_multiply]; simp
    simp only [fD]
    rw [e]
    exact hmul _ _ (fromBlocks_mem R S _ _ h1R (unitary_ch a)) (fromBlocks_mem R S _ _ h1R (unitary_ch b))
  have hcD : Continuous fD := by
    refine hc.comp_continuous ?_ (fun a => fromBlocks_mem R S _ _ h1R (unitary_ch a))
    exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const continuous_subtype_val
  have hnD : ∀ a, ‖fD a‖ = 1 :=
    norm_eq_one_of_compact fD hmD hcD (hnz _ (fromBlocks_mem R S _ _ h1R (unitary_ch 1)))
  obtain ⟨y, hy⟩ := GlobalTheory.UpqChar.char_unitary fD hmD hnD hcD
  refine ⟨x, y, fun a d ha hd => ?_⟩
  have maU : a ∈ Matrix.unitaryGroup (Fin R) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact ha
  have mdU : d ∈ Matrix.unitaryGroup (Fin S) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact hd
  have e : Matrix.fromBlocks a 0 0 d = Matrix.fromBlocks a 0 0 (1 : Matrix (Fin S) (Fin S) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0 d := by
    rw [Matrix.fromBlocks_multiply]; simp
  rw [e, hmul _ _ (fromBlocks_mem R S _ _ ha h1S) (fromBlocks_mem R S _ _ h1R hd)]
  have hA := hx ⟨a, maU⟩
  have hD := hy ⟨d, mdU⟩
  simp only [fA, fD] at hA hD
  rw [hA, hD]

end GlobalTheory.KChar
