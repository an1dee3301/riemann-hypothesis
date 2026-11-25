module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CuspDeriv

theorem continuous_deriv_of_bounded {G : Type} [TopologicalSpace G] {f f₁ f₂ : G → ℝ → ℂ}
    (hf : ∀ t, Continuous fun g => f g t) (h₁ : ∀ g t, HasDerivAt (f g) (f₁ g t) t)
    (h₂ : ∀ g t, HasDerivAt (f₁ g) (f₂ g t) t) {B : ℝ} (hB : ∀ g t, ‖f₂ g t‖ ≤ B) : Continuous fun g => f₁ g 0 := by
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB g₀ 0)
  obtain ⟨h, h0, hh⟩ : ∃ h : ℝ, 0 < h ∧ (B + B) * h < ε :=
    ⟨ε / (B + B + 1), by positivity, by rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; linarith⟩
  have hc : Continuous fun g => ‖f g h - f g₀ h‖ + ‖f g 0 - f g₀ 0‖ + (B + B) * h * h :=
    ((((hf h).sub continuous_const).norm).add ((hf 0).sub continuous_const).norm).add continuous_const
  have := (hc.tendsto g₀).eventually_lt_const (u := h * ε) (by simp only [sub_self, norm_zero, zero_add]; nlinarith)
  filter_upwards [this] with g hg
  have key := mul_norm_deriv_le (f := fun t => f g t - f g₀ t) (f₁ := fun t => f₁ g t - f₁ g₀ t)
    (f₂ := fun t => f₂ g t - f₂ g₀ t) (fun t => (h₁ g t).sub (h₁ g₀ t)) (fun t => (h₂ g t).sub (h₂ g₀ t)) h0.le
    (B := B + B) fun t _ => (norm_sub_le _ _).trans (add_le_add (hB g t) (hB g₀ t))
  rw [dist_eq_norm]
  exact lt_of_mul_lt_mul_left (key.trans_lt hg) h0.le

theorem cuspForm_mem_decay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F,
    IsCuspForm θ V F → F ∈ Decay θ V := by
  intro hP D θ hθ V F ⟨ha, hc⟩
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hd : ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) → IsRapidDecay θ V (word θ V l F) :=
    isRapidDecay_foldr_Rder hP hθ ha.toIsAutFun ha.smooth ha.growth hc
  refine ⟨ha.smooth, ha.left, fun l hl => ⟨?_, hd l hl⟩⟩
  induction l with
  | nil => exact ha.cont
  | cons p l ih =>
    have hp := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (by simp [hq])
    have hs : word θ V l F ∈ SmFun θ V :=
      (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
        fun q hq => linOnSm_Rder (hl' q hq)).mem F ha.smooth
    obtain ⟨B, hB⟩ := (hd (p :: p :: l) (List.forall_mem_cons.2 ⟨hp, hl⟩)).bounded
    have := continuous_deriv_of_bounded (f := fun g t => word θ V l F (g * oneP θ V p.1 p.2 t))
      (fun t => (ih hl').comp (continuous_mul_const _)) (hasDerivAt_oneP hθ hp (hasDerivAt_Rder hs hp))
      (hasDerivAt_oneP hθ hp (hasDerivAt_Rder (Rder_mem hs hp) hp)) fun g t => hB _
    simp only [oneP_zero hθ, mul_one] at this
    exact this

end GlobalTheory.Mem.CuspDeriv

end
