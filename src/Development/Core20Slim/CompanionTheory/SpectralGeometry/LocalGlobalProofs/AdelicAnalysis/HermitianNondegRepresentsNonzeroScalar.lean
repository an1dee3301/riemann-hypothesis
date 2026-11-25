module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.EqIdOfFixed
public import Batteries.Logic
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermRep

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_sig_fixed (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x :=
  _root_.Bl.EqIdOfFixed.goal1 h hx

end Fixed

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (T : Matrix (Fin M) (Fin M) E)

theorem hE_add_left (x x' y : Fin M → E) :
    hE σ T (x + x') y = hE σ T x y + hE σ T x' y := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hE_add_right (x y y' : Fin M → E) :
    hE σ T x (y + y') = hE σ T x y + hE σ T x y' := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_single (i j : Fin M) (a b : E) :
    hE σ T (Pi.single i a) (Pi.single j b) = σ a * T i j * b := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · simp

end Form

theorem exists_repr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ T → ∃ (t : F) (x : Fin (n + 1) → E), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  intro F E _ _ _ _ _ σ hσ n T hT
  obtain ⟨hH, hdet⟩ := hT
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    obtain ⟨t, ht⟩ := exists_of_sig_fixed hσ (hH i i)
    refine ⟨t, Pi.single i 1, ?_, ?_⟩
    · rintro rfl
      exact hi (by rw [← ht, map_zero])
    · rw [hE_single, ht]; simp
  · push_neg at hd
    obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hdet (by rw [show T = 0 from Matrix.ext hc, Matrix.det_zero])
    have hne : i ≠ j := by
      rintro rfl
      exact hij (hd i)
    refine ⟨2, Pi.single i (σ (T i j)⁻¹) + Pi.single j 1, two_ne_zero, ?_⟩
    have hji : T j i = σ (T i j) := (hH j i).symm
    have hs : σ (σ (T i j)⁻¹) = (T i j)⁻¹ := sig_sig hσ _
    rw [hE_add_left, hE_add_right, hE_add_right, hE_single, hE_single, hE_single, hE_single,
      hd i, hd j, hs, hji, map_one, map_ofNat, map_inv₀]
    have h1 : σ (T i j) ≠ 0 := (map_ne_zero _).2 hij
    field_simp
    ring

end GlobalTheory.CompanionTheory.SW.HermRep
