module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_trace_ne_zero {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) {a : E} (ha : a ≠ 0) : ∃ c : E, c * a + τ (c * a) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hE.basis
  have h1 := hcon 1
  have h2 := hcon u
  simp only [one_mul, map_mul] at h1 h2
  have hta : τ a = -a := by linear_combination h1
  rw [hta] at h2
  obtain ⟨w', hw'⟩ := hu.exists_left_inv
  apply ha
  linear_combination w' * h2 - a * hw'

theorem exists_unit_norm (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V)
    (hV : Nontrivial V) : ∃ w : V, IsUnit (B.h w w) := by
  have key : ∀ w : V, B.h w w ≠ 0 → IsUnit (B.h w w) := fun w hw =>
    hE.fixedUnit _ (B.self_fixed hE.inv w) hw
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hex : ∃ w, B.h v w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (B.nondeg v hcon)
  obtain ⟨w, hvw⟩ := hex
  obtain ⟨c, hc⟩ := exists_trace_ne_zero hE hvw
  by_cases hww : B.h w w = 0
  · by_cases hvv : B.h v v = 0
    · refine ⟨w + c • v, key _ ?_⟩
      have expand : B.h (w + c • v) (w + c • v) = c * B.h v w + τ (c * B.h v w) := by
        rw [B.add_left, B.add_right, B.add_right, B.smul_left, B.smul_left, B.smul_right,
          B.smul_right, hww, hvv, B.symm v w, map_mul]
        ring
      rw [expand]
      exact hc
    · exact ⟨v, key v hvv⟩
  · exact ⟨w, key w hww⟩

end GlobalTheory.CompanionTheory.UnrDens
