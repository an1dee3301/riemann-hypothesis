module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSq
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Init.Classical
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
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_trace_one {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (h : IsUnrQuad R σ ϖ q ε) : ∃ u θ : R, IsUnit (u - σ u) ∧ θ + σ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hσ : σ (u - σ u) = -(u - σ u) := by rw [map_sub, h.inv]; ring
  have hsv : σ v = -v := by
    have h1 : σ (u - σ u) * σ v = 1 := by rw [← map_mul, hv, map_one]
    rw [hσ] at h1
    have h2 : (u - σ u) * (σ v + v) = 0 := by linear_combination (-1 : R) * h1 + hv
    have h3 : v * ((u - σ u) * (σ v + v)) = 0 := by rw [h2, mul_zero]
    rw [← mul_assoc, mul_comm v, hv, one_mul] at h3
    linear_combination h3
  refine ⟨u, u * v, hu, ?_⟩
  rw [map_mul, hsv]
  linear_combination hv

theorem hermMod_eq {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (h : IsUnrQuad R σ ϖ q ε) (n k : ℕ) :
    hermMod σ ϖ n k = {H | ∀ a b, barσ σ ϖ h.fix_ϖ k (H b a) = H a b} := by
  ext H
  simp only [PositivityTheory.PfSWUS.Loc.hermMod, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, hh, rfl⟩ a b
    have hab := congrFun (congrFun hh a) b
    simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply] at hab
    simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, barσ_mk]
    rw [hab]
  · intro hH
    obtain ⟨-, θ, -, hθ⟩ := exists_trace_one h
    choose lift hlift using fun a b => Ideal.Quotient.mk_surjective (H a b)
    refine ⟨Matrix.of fun a b => θ * lift a b + σ (θ * lift b a), ?_, ?_⟩
    · ext a b
      simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_add (f := _),
        h.inv]
      ring
    · ext a b
      have e1 : Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (σ (lift b a)) = barσ σ ϖ h.fix_ϖ k (H b a) := by
        rw [← hlift b a, barσ_mk]
      have hθ' : Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) θ + Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (σ θ) = 1 := by
        rw [← map_add (f := _), hθ, map_one]
      simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.of_apply, map_add (f := _), map_mul, hlift]
      rw [e1, hH a b]
      linear_combination (H a b) * hθ'

theorem card_hermMod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  intro R _ σ ϖ q ε h n k
  rw [hermMod_eq h n k]
  have hcard := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε h k
  have hq : 1 < q := h.one_lt
  haveI : Finite (R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  obtain ⟨u, hu, -⟩ := h.basis
  have hinv : ∀ x, barσ σ ϖ h.fix_ϖ k (barσ σ ϖ h.fix_ϖ k x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [barσ_mk, barσ_mk, h.inv]
  have hω : IsUnit (Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) u -
      barσ σ ϖ h.fix_ϖ k (Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) u)) := by
    rw [barσ_mk, ← map_sub]
    exact hu.map _
  have key := GlobalTheory.GramCount.card_hermitian_dvd_sq (barσ σ ϖ h.fix_ϖ k) hinv _ hω 1 (map_one _) n
  have e2 : Nat.card {x : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k // (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ x} = q ^ (2 * k) := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)
  apply Nat.pow_left_injective two_ne_zero
  show _ ^ 2 = _ ^ 2
  calc Nat.card ↥{H : Matrix (Fin n) (Fin n) (R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) |
          ∀ a b, barσ σ ϖ h.fix_ϖ k (H b a) = H a b} ^ 2
      = Nat.card {H : Fin n → Fin n → R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k //
          (∀ a b : Fin n, barσ σ ϖ h.fix_ϖ k (H b a) = H a b) ∧
            ∀ a b : Fin n, (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ H a b} ^ 2 := by
        congr 1
        exact Nat.card_congr
          { toFun := fun H => ⟨H.1, H.2, fun _ _ => one_dvd _⟩
            invFun := fun H => ⟨H.1, H.2.1⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    _ = Nat.card {x : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k // (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ x} ^ (n * n) := key
    _ = (q ^ (k * n ^ 2)) ^ 2 := by
        rw [e2, ← pow_mul, ← pow_mul]
        ring_nf

end GlobalTheory.CompanionTheory.UnrDens
