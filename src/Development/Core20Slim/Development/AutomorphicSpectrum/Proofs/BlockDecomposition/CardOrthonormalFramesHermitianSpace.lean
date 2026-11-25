module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCardStatement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Zify

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.OrthCount

variable {E : Type} [CommRing E] {τ : E →+* E} {V : Type} [AddCommGroup V] [Module E V]

abbrev Tuples (B : HermSp E τ V) (n : ℕ) : Type :=
  {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0}

theorem isUnit_norm (B : HermSp E τ V) (w : {w : V // B.h w w = 1}) : IsUnit (B.h w.1 w.1) := by
  rw [w.2]; exact isUnit_one

noncomputable def consEquiv (B : HermSp E τ V) (n : ℕ) :
    Tuples B (n + 1) ≃
      Σ w : {w : V // B.h w w = 1}, Tuples (B.perpForm (isUnit_norm B w)) n where
  toFun x := ⟨⟨x.1 0, by simpa using x.2 0 0⟩,
    ⟨fun j => ⟨x.1 j.succ, by
      show B.h (x.1 j.succ) (x.1 0) = 0
      simpa [Fin.succ_ne_zero] using x.2 j.succ 0⟩, fun i j => by
      simpa using x.2 i.succ j.succ⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun j => (p.2.1 j : V)), by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hw
    · have h0 : B.h (y j : V) w = 0 := (y j).2
      simp [B.symm (y j : V) w, h0, (Fin.succ_ne_zero j).symm]
    · have h0 : B.h (y i : V) w = 0 := (y i).2
      simp [h0, Fin.succ_ne_zero i]
    · simpa using hy i j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    rfl

end GlobalTheory.CompanionTheory.UnrDens.OrthCount

namespace GlobalTheory.CompanionTheory.UnrDens


open OrthCount in
theorem card_orthonormal_tuples : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  intro E _ τ q ε hR n
  induction n with
  | zero =>
    intro m _ V _ _ B _
    have h1 : Nat.card {x : Fin 0 → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩
    simp [h1]
  | succ n ih =>
    intro m hnm V _ _ B hc
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq : 1 < q := hR.one_lt
    have hq0 : q ≠ 0 := by omega
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hq0)
    haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hR.card]; exact pow_ne_zero _ hq0)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hR.card]; nlinarith)
    have hsph := (GlobalTheory.T.hermitian_vector_values_card E τ q ε hR (m' + 1) V B hc).1 1 (map_one τ) one_ne_zero
    have hperp : ∀ w : {w : V // B.h w w = 1}, Nat.card (B.perp w.1) = q ^ (2 * m') := by
      intro w
      have h1 := Nat.card_congr (B.perpEquiv (isUnit_norm B w))
      rw [Nat.card_prod, hR.card, hc] at h1
      have h2 : q ^ (2 * (m' + 1)) = q ^ 2 * q ^ (2 * m') := by ring
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 2) h1
    have hfib : ∀ w : {w : V // B.h w w = 1},
        (Nat.card (Tuples (B.perpForm (isUnit_norm B w)) n) : ℝ) =
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) :=
      fun w => ih m' (by omega) (B.perp w.1) (B.perpForm (isUnit_norm B w)) (hperp w)
    haveI : Fintype {w : V // B.h w w = 1} := Fintype.ofFinite _
    have hcard : (Nat.card (Tuples B (n + 1)) : ℝ) =
        (Nat.card {w : V // B.h w w = 1} : ℝ) *
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) := by
      rw [Nat.card_congr (consEquiv B n), Nat.card_sigma]
      push_cast
      rw [Finset.sum_congr rfl (fun w _ => hfib w), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
    change (Nat.card (Tuples B (n + 1)) : ℝ) = _
    rw [hcard, hsph, Fin.prod_univ_succ]
    simp [Nat.add_sub_add_right]

end GlobalTheory.CompanionTheory.UnrDens
