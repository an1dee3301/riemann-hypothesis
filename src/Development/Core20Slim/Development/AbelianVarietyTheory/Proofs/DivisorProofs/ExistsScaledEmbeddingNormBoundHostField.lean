module

public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.GNorm

theorem entry_bound {ι κ E : Type} [Fintype κ] [DecidableEq κ] [Ring E] {m n : ℕ}
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) (s : κ → ℝ) (hs : ∀ k, 0 < s k)
    (B : ι → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ))
    (ξ : Matrix (Fin m) (Fin n) E) (τ : ι) (k : κ) (j : Fin n) :
    ‖σ τ ((T * ξ) k j)‖ / s k ≤ ∑ i, ‖T.map (σ τ) k i‖ * ‖(B τ * ξ.map (σ τ)) i j‖ := by
  have hmap : σ τ ((T * ξ) k j) = (T.map (σ τ) * ξ.map (σ τ)) k j := by
    rw [← Matrix.map_mul]; rfl
  have key : ((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j) = (T.map (σ τ) * (B τ * ξ.map (σ τ))) k j := by
    rw [hmap, ← Matrix.mul_assoc, hB τ, Matrix.mul_assoc, Matrix.diagonal_mul]
  have hnorm : ‖σ τ ((T * ξ) k j)‖ / s k = ‖((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hs k).le, div_eq_inv_mul]
  rw [hnorm, key, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ => norm_mul _ _)

theorem gnorm_gen {ι κ E : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Ring E] (m n : ℕ)
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : ι → Matrix (Fin m) (Fin m) ℂ,
      (∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ)) →
      ∀ ξ : Matrix (Fin m) (Fin n) E,
        ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤
          C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (σ τ)) i j‖ := by
  set c : ℝ := ∑ τ, ∑ k, ∑ i, ‖T.map (σ τ) k i‖ with hc
  have hc0 : 0 ≤ c := by positivity
  have hac : ∀ τ k i, ‖T.map (σ τ) k i‖ ≤ c := by
    intro τ k i
    have h1 : ‖T.map (σ τ) k i‖ ≤ ∑ i', ‖T.map (σ τ) k i'‖ :=
      Finset.single_le_sum (f := fun i' => ‖T.map (σ τ) k i'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i', ‖T.map (σ τ) k i'‖ ≤ ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ :=
      Finset.single_le_sum (f := fun k' => ∑ i', ‖T.map (σ τ) k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ k)
    have h3 : ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ ≤ c :=
      Finset.single_le_sum (f := fun τ' => ∑ k', ∑ i', ‖T.map (σ τ') k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ τ)
    linarith
  refine ⟨1 + Fintype.card κ * c, by nlinarith [hc0, (Nat.cast_nonneg (Fintype.card κ) : (0:ℝ) ≤ _)], ?_⟩
  intro s hs B hB ξ
  set b : ι → Fin m → Fin n → ℝ := fun τ i j => ‖(B τ * ξ.map (σ τ)) i j‖ with hb
  have hb0 : ∀ τ i j, 0 ≤ b τ i j := fun _ _ _ => norm_nonneg _
  have S0 : 0 ≤ ∑ τ, ∑ i, ∑ j, b τ i j := by positivity
  calc ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1
      = ∑ p : κ × Fin n, ∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖ / s p.1 := by
        simp_rw [Finset.sum_div]
    _ ≤ ∑ p : κ × Fin n, ∑ τ, ∑ i, c * b τ i p.2 := by
        gcongr with p _ τ _
        refine (entry_bound σ T s hs B hB ξ τ p.1 p.2).trans ?_
        gcongr with i _
        exact hac τ p.1 i
    _ = ∑ _k : κ, ∑ j : Fin n, ∑ τ, ∑ i, c * b τ i j := by
        rw [Fintype.sum_prod_type]
    _ = Fintype.card κ * (c * ∑ j, ∑ τ, ∑ i, b τ i j) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Finset.mul_sum]
    _ = Fintype.card κ * c * ∑ τ, ∑ i, ∑ j, b τ i j := by
        rw [mul_assoc]
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_comm]
    _ ≤ (1 + Fintype.card κ * c) * ∑ τ, ∑ i, ∑ j, b τ i j := by nlinarith

end GlobalTheory.Proof.GNorm

namespace GlobalTheory

theorem tGnorm : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E), ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤ C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ := by
  intro D κ _ _ m n T
  exact GlobalTheory.Proof.GNorm.gnorm_gen m n (tauE D) T

end GlobalTheory
