module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasBrg
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AutomorphicArithmetic.CrystallineRing.Acris0
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfEmbUnique
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix 
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.IndefR.Eqv

theorem norm_mul_mul_apply_le {n : ℕ} (P A Q : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hA : ∀ k l, ‖A k l‖ ≤ c)
    (i j : Fin n) : ‖(P * A * Q) i j‖ ≤ (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
  simp only [Matrix.mul_apply]
  calc ‖∑ l, (∑ k, P i k * A k l) * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * c * ‖Q l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, ← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hA k l) (norm_nonneg _)
    _ = (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring


variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}








end GlobalTheory.CuspGeo
