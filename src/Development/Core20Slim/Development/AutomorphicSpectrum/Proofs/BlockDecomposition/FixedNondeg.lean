module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.SiegLoc

variable {R : Type} [CommRing R]

theorem psi_pow {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (Ideal.Quotient.mk _ (ϖ ^ j * a)) = ψ k (Ideal.Quotient.mk _ a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', mul_assoc]
    exact hψ.compat (k + j) (ϖ ^ j * a)

theorem mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

theorem fixed_nondeg {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ) (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R)
    (ha : σ a = a) (h : ∀ b, σ b = b → ψ k (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev ϖ k := by
  induction k generalizing a with
  | zero => simp [lev]
  | succ k ih =>
    have ha' : a ∈ lev ϖ k := ih a ha (fun b hb => by
      have := h (ϖ * b) (by simp [hfix, hb])
      rw [show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat] at this
      exact this)
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 ha'
    have hregk : IsSMulRegular R (ϖ ^ k) := hreg.pow k
    have hc : σ c = c := by
      apply hregk
      simpa [map_mul, map_pow, hfix] using ha
    have hc1 : c ∈ lev ϖ 1 := hψ.prim c hc (fun b hb => by
      have h1 := h b hb
      have h2 := psi_pow hψ 1 k (c * b)
      rw [Nat.add_comm 1 k, ← mul_assoc] at h2
      rw [← h2]; exact h1)
    obtain ⟨d, rfl⟩ := mem_lev_iff.1 hc1
    exact mem_lev_iff.2 ⟨d, by ring⟩

theorem trace_nondeg {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ) (k : ℕ) (y : R)
    (h : ∀ t, ψ k (Ideal.Quotient.mk _ (t * y + σ (t * y))) = 1) : y ∈ lev ϖ k := by
  obtain ⟨u, hu, -⟩ := hR.basis
  have key : ∀ t, t * y + σ (t * y) ∈ lev ϖ k := fun t => by
    refine fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) (fun b hb => ?_)
    have := h (b * t)
    convert this using 3
    simp only [map_mul, hb]; ring
  have h1 := key 1
  have h2 := key u
  have h3 : (u - σ u) * y ∈ lev ϖ k := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ _ h1)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.CompanionTheory.SiegLoc
end
