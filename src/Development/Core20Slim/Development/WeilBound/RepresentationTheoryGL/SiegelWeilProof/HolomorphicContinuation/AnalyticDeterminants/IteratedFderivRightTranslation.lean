module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Prelude
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulR (c : M2 n) : M2 n →L[ℂ] M2 n := (LinearMap.mulRight ℂ c).toContinuousLinearMap

theorem mulR_apply (c y : M2 n) : mulR c y = y * c := rfl



theorem iterated_fderiv_right_translation {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) := by
  classical
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ N F) x :=
    hFx.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top N)
  have hg : ∀ i : Fin N, HasFDerivAt (fun y : M2 n => y * W i.succ) (mulR (W i.succ)) x :=
    fun i => (mulR (W i.succ)).hasFDerivAt
  have h := hd.hasFDerivAt.continuousMultilinearMap_apply (g := fun i y => y * W i.succ) hg
  have hz : ∀ i : Fin N, mulR (W i.succ) (x * W 0) = 0 := fun i => by
    rw [mulR_apply, mul_assoc, hW, mul_zero]
  refine (congrArg (fun L => L (x * W 0)) h.fderiv).trans ?_
  have hs : ∀ L : Fin N → (M2 n →L[ℂ] ℂ), (∀ i, L i (x * W 0) = 0) → (∑ i, L i) (x * W 0) = 0 := by
    intro L hL
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hL i
  rw [ContinuousLinearMap.add_apply, hs _ (fun i => by rw [ContinuousLinearMap.comp_apply, hz, map_zero]), add_zero,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_succ_apply_left]
  rfl









theorem cont_on_K (H : M2 n → ℂ) (hH : ContDiffOn ℂ ∞ H (Dom n)) (Kg : Type) [TopologicalSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) (hdom : ∀ k, ι k ∈ Dom n) : Continuous (fun k => H (ι k)) :=
  hH.continuousOn.comp_continuous hι hdom


end PositivityTheory.Rg.Sw.LVs
