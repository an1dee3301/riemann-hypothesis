module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusConeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalisingStatement
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
public import Init.Data.Rat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusStack

theorem lattice_count_stack : ∀ (D : D7) (m n r : ℕ) (X Y : Matrix (Fin m) (Fin r) D.host.E) (X' Y' : Matrix (Fin r) (Fin m) D.host.E) (c : ℝ), 0 < c → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, Y'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map (tauE D τ) ∧ X'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map (tauE D τ) ∧ (1 - X * Y' - Y * X').map (tauE D τ) * B τ = (1 - X * Y' - Y * X').map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D m n r X Y X' Y' c hc L hL
  have hST : Matrix.fromCols X (Matrix.fromCols Y (1 : Matrix (Fin m) (Fin m) D.host.E)) *
      Matrix.fromRows Y' (Matrix.fromRows X' (1 - X * Y' - Y * X')) = 1 := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.one_mul]
    abel
  obtain ⟨N, C, hC, h⟩ := GlobalTheory.T.latticeCount_sum_bound_of_rational_diagonalising D (Fin r ⊕ Fin r ⊕ Fin m) m n _ _ hST L hL
  obtain ⟨C', hC', h'⟩ := GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone r m (Module.finrank ℚ D.host.F * (2 * n)) c hc
  refine ⟨N, C * C', mul_nonneg hC hC', fun t ht B hB => ?_⟩
  have htpos : ∀ i, 0 < t i := ht.1
  refine (h (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ)))) ?_ B ?_).trans ?_
  · rintro (k | k | k)
    · exact htpos k
    · exact inv_pos.2 (htpos k)
    · exact one_pos
  · intro τ
    obtain ⟨h1, h2, h3⟩ := hB τ
    ext k j
    rcases k with k | k | k
    · have := congrFun (congrFun h1 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h2 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h3 k) j
      rw [Matrix.diagonal_mul]
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.fromRows_apply_inr, Sum.elim_inr,
        Complex.ofReal_one, inv_one, one_mul] at this ⊢
      exact this
  · apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h' t ht) hC

end GlobalTheory.TorusStack
