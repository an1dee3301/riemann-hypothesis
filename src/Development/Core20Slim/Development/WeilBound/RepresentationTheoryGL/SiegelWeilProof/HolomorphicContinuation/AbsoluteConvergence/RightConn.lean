module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open GlobalTheory.Cont


theorem glue : Glue := by
  intro U f h σ s₀ hUo hU hs₀ hfm hfa hσU hhd hfh
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ w, H w = if σ + 1 < w.re then h w else f w := ⟨_, fun _ => rfl⟩
  have hHf : ∀ z, H =ᶠ[𝓝[≠] z] f := by
    intro z
    by_cases hz : σ < z.re
    · filter_upwards [hfh z hz] with w hw
      rw [hH]
      split_ifs
      · exact hw.symm
      · rfl
    · have hlt : z.re < σ + 1 := by linarith [not_lt.1 hz]
      have hn : {w : ℂ | w.re < σ + 1} ∈ 𝓝 z :=
        Complex.continuous_re.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt)
      filter_upwards [nhdsWithin_le_nhds hn] with w hw
      rw [hH, if_neg (not_lt.2 (le_of_lt hw))]
  have hmer : IsMerExt h U H := by
    refine ⟨hU, fun z hz => (hfm z hz).congr (hHf z).symm, σ + 1, fun z hz => ?_⟩
    rw [hH, if_pos (show σ + 1 < z.re from hz)]
  have hext : IsExtAt h s₀ (Function.update H s₀ (f s₀)) := (hmer.isExtAt hs₀).update _
  refine ⟨_, hext, ?_, by simp⟩
  apply hfa.congr
  have h2 := eventually_nhdsWithin_iff.1 (hHf s₀)
  filter_upwards [h2] with w hw
  by_cases hw0 : w = s₀
  · subst hw0
    simp
  · rw [Function.update_of_ne hw0]
    exact (hw hw0).symm

end PositivityTheory.Rg.Sw.AbsSt
