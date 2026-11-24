module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
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
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.FockTDec

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

section General

variable {σ : Type}

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  zero_mem' := fun P => by simp
  add_mem' := fun {L L'} h h' P => by
    rw [LinearMap.add_apply]
    exact (totalDegree_add _ _).trans (max_le (h P) (h' P))
  smul_mem' := fun c L h P => by
    rw [LinearMap.smul_apply]
    exact (totalDegree_smul_le _ _).trans (h P)

theorem one_mem : (1 : Module.End ℂ (MvPolynomial σ ℂ)) ∈ nonRaising σ := fun _ => le_rfl

theorem mul_mem {L L' : Module.End ℂ (MvPolynomial σ ℂ)} (h : L ∈ nonRaising σ) (h' : L' ∈ nonRaising σ) :
    L * L' ∈ nonRaising σ := fun P => (h _).trans (h' P)

theorem totalDegree_X_mul_pderiv (x y : σ) (P : MvPolynomial σ ℂ) :
    (X x * pderiv y P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s y = 0
  · simp [h0]
  · have hs' : (Finsupp.single y 1) + (s - Finsupp.single y 1) = s := by
      rw [add_tsub_cancel_of_le]
      rw [Finsupp.single_le_iff]; omega
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    refine le_trans ?_ (le_totalDegree hs)
    have h1 := totalDegree_monomial_le (s - Finsupp.single y 1) (AddMonoidAlgebra.coeff P s * (s y : ℂ))
    have h2 : (s.sum fun _ e => e) = 1 + (s - Finsupp.single y 1).sum fun _ e => e := by
      conv_lhs => rw [← hs']
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [h2]
    exact Nat.add_le_add_left h1 1

theorem pderiv_mem (y : σ) : (pderiv y).toLinearMap ∈ nonRaising σ := by
  intro P
  change (pderiv y P).totalDegree ≤ _
  by_cases h : pderiv y P = 0
  · simp [h]
  · refine le_trans ?_ (totalDegree_X_mul_pderiv y y P)
    rw [totalDegree_mul_of_isDomain (X_ne_zero y) h]
    omega

theorem mul_pderiv_mem (x y : σ) :
    LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) * (pderiv y).toLinearMap ∈ nonRaising σ :=
  fun P => totalDegree_X_mul_pderiv x y P

theorem pderiv_mul_mem (x y : σ) :
    (pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) ∈ nonRaising σ := by
  classical
  intro P
  have e : ((pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) :
      Module.End ℂ (MvPolynomial σ ℂ)) P = pderiv y (X x * P) := rfl
  rw [e]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (totalDegree_add _ _).trans (max_le (totalDegree_X_mul_pderiv x y P) ?_)
  by_cases h : x = y
  · subst h; rw [pderiv_X_self, mul_one]
  · rw [pderiv_X_of_ne h, mul_zero, totalDegree_zero]; exact Nat.zero_le _

end General

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def quad (i l : Fin b) (j : Fin a) : PolF D b a :=
  if ε' i = ε j ∧ ε' l ≠ ε j then X (τ, i, j) * X (τ, l, j) else 0

theorem sgn_mul_self (e : Bool) : sgn e * sgn e = 1 := by
  cases e <;> simp [sgn]

theorem term_mem (i l : Fin b) (j : Fin a) :
    raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j) ∈ nonRaising (FVar D b a) := by
  unfold raiO lowO quad
  rw [smul_mul_smul_comm, sgn_mul_self, one_smul]
  by_cases hi : ε' i = ε j <;> by_cases hl : ε' l = ε j
  · simp only [hi, hl, if_true, ne_eq, not_true, and_false, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero]
    exact mul_pderiv_mem _ _
  · simp only [hi, hl, if_true, ne_eq, not_false_iff, and_self, if_false]
    rw [LinearMap.mulLeft_mul, Module.End.mul_eq_comp, sub_self]
    exact Submodule.zero_mem _
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (mul_mem (pderiv_mem _) (pderiv_mem _))
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (pderiv_mul_mem _ _)

def quadAll (Y : Matrix (Fin b) (Fin b) ℂ) : PolF D b a :=
  ∑ i, ∑ l, Y i l • ∑ j, quad τ ε ε' i l j

theorem quadAll_hom (Y : Matrix (Fin b) (Fin b) ℂ) : (quadAll τ ε ε' Y).IsHomogeneous 2 := by
  rw [← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => ?_)
  unfold quad
  split_ifs
  · exact (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)
  · exact Submodule.zero_mem _

theorem fockQuadraticPart_ne_zero_of_offBlock_entry (Y : Matrix (Fin b) (Fin b) ℂ) (i₀ l₀ : Fin b) (j₀ : Fin a) (hi : ε' i₀ = ε j₀)
    (hl : ε' l₀ ≠ ε j₀) (hY : Y i₀ l₀ ≠ 0) : quadAll τ ε ε' Y ≠ 0 := by
  classical
  intro h0
  let pt : FVar D b a → ℂ := fun v => if v = (τ, i₀, j₀) ∨ v = (τ, l₀, j₀) then 1 else 0
  have hq : ∀ i l j, eval pt (quad τ ε ε' i l j) = if j = j₀ ∧ l = l₀ ∧ i = i₀ then 1 else 0 := by
    intro i l j
    unfold quad
    by_cases hc : ε' i = ε j ∧ ε' l ≠ ε j
    · rw [if_pos hc, map_mul, eval_X, eval_X]
      by_cases hj : j = j₀
      · subst hj
        have h1 : i ≠ l₀ := fun h => hl (h ▸ hc.1)
        have h2 : l ≠ i₀ := fun h => hc.2 (h ▸ hi)
        by_cases h3 : i = i₀ <;> by_cases h4 : l = l₀ <;> simp [pt, h1, h2, h3, h4]
      · simp [pt, hj]
    · rw [if_neg hc, map_zero, if_neg]
      rintro ⟨rfl, rfl, rfl⟩
      exact hc ⟨hi, hl⟩
  have := congrArg (eval pt) h0
  unfold quadAll at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, smul_eval, hq, map_zero, ite_and] at this
  apply hY
  simpa using this

theorem sub_mem (Y : Matrix (Fin b) (Fin b) ℂ) :
    fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) ∈ nonRaising (FVar D b a) := by
  have : fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
      ∑ i, ∑ l, Y i l • ∑ j, ((raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j)) +
        if i = l then (1 / 2 : ℂ) • 1 else 0) := by
    have hm : LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
        ∑ i, ∑ l, Y i l • ∑ j, LinearMap.mulLeft ℂ (quad τ ε ε' i l j) := by
      refine LinearMap.ext fun P => ?_
      simp [quadAll, Finset.sum_mul, LinearMap.sum_apply]
    rw [hm]
    unfold fockT
    simp only [← Finset.sum_sub_distrib, ← smul_sub]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    abel
  rw [this]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ (term_mem τ ε ε' i l j) ?_)
  split_ifs
  · exact Submodule.smul_mem _ _ one_mem
  · exact Submodule.zero_mem _

theorem fockT_decomp : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin b) (Fin b) ℂ), 0 < a → (∃ i l, ε' i ≠ ε' l ∧ Y i l ≠ 0 ∧ Y l i ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y = LinearMap.mulLeft ℂ Q + L := by
  rintro D a b τ ε ε' Y ha ⟨i, l, hil, h1, h2⟩
  refine ⟨quadAll τ ε ε' Y, _, ?_, quadAll_hom τ ε ε' Y, sub_mem τ ε ε' Y, by abel⟩
  by_cases h : ε' i = ε ⟨0, ha⟩
  · exact fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y i l ⟨0, ha⟩ h (fun h' => hil (h.trans h'.symm)) h1
  · refine fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y l i ⟨0, ha⟩ ?_ h h2
    revert h hil
    cases ε' i <;> cases ε' l <;> cases ε ⟨0, ha⟩ <;> simp

end GlobalTheory.Chain.FockTDec

end
