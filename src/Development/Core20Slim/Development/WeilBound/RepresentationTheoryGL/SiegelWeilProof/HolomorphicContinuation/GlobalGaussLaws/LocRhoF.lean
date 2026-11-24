module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {n : ℕ}

def reIm {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
  else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def reImInv {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
  else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem evX_eq_zero {m : ℕ} (P : PX m n) (h : ∀ u : Fin m → Fin n → ℂ, evX P u = 0) : P = 0 := by
  have h2 : (C (1 / 2 : ℂ) + C (1 / 2) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = 1 := by
    rw [← C_add, ← C_1]
    norm_num
  have hI : (C Complex.I * C (1 / (2 * Complex.I)) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = C (1 / 2) := by
    rw [← C_mul]
    congr 1
    field_simp
  have hinv : ∀ k, bind₁ reImInv (reIm (n := n) (m := m) k) = X k := by
    rintro ⟨a, i, b⟩
    cases b
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination (X (a, i, false) - X (a, i, true)) * hI + X (a, i, false) * h2
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hI + X (a, i, true) * h2
  have hQ : bind₁ reIm P = 0 := by
    apply GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real
    intro u
    let z : Fin m → Fin n → ℂ := fun a i => (u (a, i, false) : ℂ) + Complex.I * (u (a, i, true) : ℂ)
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ reIm P) = 0
    rw [eval₂Hom_bind₁]
    have hf : (fun k => eval₂Hom (RingHom.id ℂ) (fun v => ((u v : ℝ) : ℂ)) (reIm (n := n) (m := m) k)) =
        fun k => if k.2.2 = true then star (z k.1 k.2.1) else z k.1 k.2.1 := by
      funext ⟨a, i, b⟩
      cases b
      · simp [reIm, z]
      · apply Complex.ext <;> simp [reIm, z]
    rw [hf]
    exact h z
  calc P = bind₁ reImInv (bind₁ reIm P) := by
        rw [bind₁_bind₁]
        simp only [hinv]
        rw [bind₁_X_left]
        rfl
    _ = 0 := by rw [hQ, map_zero]

theorem gs_ne_zero {m : ℕ} (c : ℝ) (u : Fin m → Fin n → ℂ) : gs c u ≠ 0 := Complex.exp_ne_zero _

theorem fP_inj {m : ℕ} (c : ℝ) {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  have h0 : P - Q = 0 := by
    apply evX_eq_zero
    intro u
    have := congrFun h u
    unfold fP at this
    have h2 := mul_right_cancel₀ (gs_ne_zero c u) this
    unfold evX at h2 ⊢
    rw [map_sub, h2, sub_self]
  exact sub_eq_zero.1 h0

theorem fP_add_smul {m : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add (f := _), MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
