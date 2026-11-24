module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix

namespace GlobalTheory

theorem eichlerTransvection_unitary_inverse_conj :
    ∀ (A : Type) [CommRing A] [StarRing A] [Invertible (2 : A)] (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι A) (_ : Gᴴ = G) (h : (ι → A) → (ι → A) → A) (_ : ∀ x y, h x y = star y ⬝ᵥ G.mulVec x) (E : (ι → A) → (ι → A) → (ι → A) → (ι → A)) (_ : ∀ w v y, E w v y = y + h y v • w - h y w • v - (⅟(2 : A) * h v v * h y w) • w), (∀ w v, h w w = 0 → h w v = 0 → ∀ x y, h (E w v x) (E w v y) = h x y) ∧ (∀ w v, h w w = 0 → h w v = 0 → ∀ y, E w (-v) (E w v y) = y) ∧ ∀ (g : Matrix ι ι A), (∀ x y, h (g.mulVec x) (g.mulVec y) = h x y) → ∀ w v y, g.mulVec (E w v y) = E (g.mulVec w) (g.mulVec v) (g.mulVec y) := by
  intro A _ _ _ ι _ _ G hG h hh E hE
  have addl : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y; simp only [hh, mulVec_add, dotProduct_add]
  have subl : ∀ x x' y, h (x - x') y = h x y - h x' y := by
    intro x x' y; simp only [hh, mulVec_sub, dotProduct_sub]
  have negl : ∀ x y, h (-x) y = - h x y := by
    intro x y; simp only [hh, mulVec_neg, dotProduct_neg]
  have smull : ∀ (a : A) x y, h (a • x) y = a * h x y := by
    intro a x y; simp only [hh, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have addr : ∀ x y y', h x (y + y') = h x y + h x y' := by
    intro x y y'; simp only [hh, star_add, add_dotProduct]
  have subr : ∀ x y y', h x (y - y') = h x y - h x y' := by
    intro x y y'; simp only [hh, star_sub, sub_dotProduct]
  have negr : ∀ x y, h x (-y) = - h x y := by
    intro x y; simp only [hh, star_neg, neg_dotProduct]
  have smulr : ∀ (a : A) x y, h x (a • y) = star a * h x y := by
    intro a x y; simp only [hh, star_smul, smul_dotProduct, smul_eq_mul]
  have symm : ∀ x y, star (h x y) = h y x := by
    intro x y
    rw [hh, hh, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self _
  have s2 : star (⅟(2 : A)) = ⅟(2 : A) := by
    have := congrArg star h2
    rw [star_mul', star_one, star_ofNat] at this
    linear_combination (⅟(2 : A)) * this - (star (⅟(2 : A))) * h2
  refine ⟨?_, ?_, ?_⟩
  · intro w v hww hwv x y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE, hE]
    simp only [addl, subl, smull, addr, subr, smulr, star_mul', symm, s2, hww, hwv, hvw]
    linear_combination (-(h v v * h x w * h w y)) * h2
  · intro w v hww hwv y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE w (-v), hE w v]
    simp only [addl, subl, smull, negl, negr, hww, hwv, hvw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (-(h v v * h y w * w i)) * h2
  · intro g hg w v y
    rw [hE, hE]
    simp only [hg, mulVec_add, mulVec_sub, mulVec_smul]

end GlobalTheory
