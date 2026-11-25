module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem norm_iteratedFDeriv_diag_multilinear_le (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
  set L : E →L[ℝ] (Fin j → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E) with hL
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 (fun _ => ?_)
    simp [hL]
  have hfun : (fun y : E => f (fun _ => y)) = (f : (Fin j → E) → ℂ) ∘ L := by
    funext z; simp [hL]
  have hf : ContDiff ℝ ⊤ (f : (Fin j → E) → ℂ) := f.contDiff
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L hf y (by exact_mod_cast le_top)]
  have hLy : ‖L y‖ ≤ ‖y‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 (fun _ => ?_)
    simp [hL]
  calc ‖(iteratedFDeriv ℝ i (⇑f) (L y)).compContinuousLinearMap (fun _ => L)‖
      ≤ ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ * ∏ _ : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
    _ = ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ := mul_one _
    _ ≤ (Fintype.card (Fin j)).descFactorial i * ‖f‖ * ‖L y‖ ^ (Fintype.card (Fin j) - i) :=
        f.norm_iteratedFDeriv_le i (L y)
    _ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
        rw [Fintype.card_fin]
        gcongr

end GlobalTheory
