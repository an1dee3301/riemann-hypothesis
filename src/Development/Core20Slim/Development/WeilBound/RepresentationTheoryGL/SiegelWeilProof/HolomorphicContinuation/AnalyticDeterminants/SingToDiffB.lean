module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffA
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace STD

variable {n : ℕ}

theorem contDiffOn_dc {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (a : Fin n × Fin n) : ContDiffOn ℝ ∞ (dc a f) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))

theorem contDiffOn_dList {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ∀ l : List (Fin n × Fin n), ContDiffOn ℝ ∞ (dList l f) U
  | [] => hf
  | a :: l => contDiffOn_dc hU (contDiffOn_dList hU hf l) a

structure IsT (U : Set (Vr n)) (φ : Vr n → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  cpt : HasCompactSupport φ
  sub : tsupport φ ⊆ U

theorem support_dc_subset (f : Vr n → ℂ) (a : Fin n × Fin n) : support (dc a f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  apply hx
  have : fderiv ℝ f x = 0 := by
    by_contra h'
    exact h (support_fderiv_subset (𝕜 := ℝ) h')
  simp [dc, this]

theorem isT_dc {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) (a : Fin n × Fin n) : IsT U (dc a φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (contDiffOn_dc isOpen_univ (contDiffOn_univ.mpr h.smooth) a)
  · exact h.cpt.mono' (support_dc_subset φ a)
  · exact (closure_minimal (support_dc_subset φ a) (isClosed_tsupport φ)).trans h.sub

theorem isT_dList {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) : ∀ l : List (Fin n × Fin n), IsT U (dList l φ)
  | [] => h
  | a :: l => isT_dc (isT_dList h l) a

theorem tsupport_dList_subset (φ : Vr n → ℂ) : ∀ l : List (Fin n × Fin n), tsupport (dList l φ) ⊆ tsupport φ
  | [] => le_rfl
  | a :: l => (closure_minimal ((support_dc_subset _ a).trans (tsupport_dList_subset φ l))
      (isClosed_tsupport φ))

theorem integrable_mul_of_contOn {U : Set (Vr n)} (hU : IsOpen U) {h φ : Vr n → ℂ} (hh : ContinuousOn h U)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x => h x * φ x) := by
  have hc' : Continuous (fun x => h x * φ x) :=
    (hh.mul hφ.continuousOn).continuous_of_tsupport_subset hU ((tsupport_mul_subset_right).trans hs)
  exact hc'.integrable_of_hasCompactSupport hc.mul_left

theorem ibp_dc {U : Set (Vr n)} (hU : IsOpen U) {F φ : Vr n → ℂ} (hF : ContDiffOn ℝ ∞ F U)
    (hφ : IsT U φ) (a : Fin n × Fin n) :
    ∫ x, F x * dc a φ x = - ∫ x, dc a F x * φ x := by
  have hFd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x := fun x hx =>
    (hF.contDiffAt (hU.mem_nhds (hφ.sub hx))).differentiableAt (by simp)
  have hφd : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x := fun x _ =>
    (hφ.smooth.differentiable (by simp)) x
  have hFc : ContinuousOn (fun x => fderiv ℝ F x) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hφc : Continuous (fun x => fderiv ℝ φ x) := hφ.smooth.continuous_fderiv (by simp)
  have hA : ∀ v : Vr n, Integrable (fun x => fderiv ℝ F x v * φ x) := fun v =>
    integrable_mul_of_contOn hU (hFc.clm_apply continuousOn_const) hφ.smooth.continuous hφ.cpt hφ.sub
  have hB : ∀ v : Vr n, Integrable (fun x => F x * fderiv ℝ φ x v) := fun v =>
    integrable_mul_of_contOn hU hF.continuousOn (hφc.clm_apply continuous_const)
      (hφ.cpt.fderiv_apply ℝ v)
      ((closure_minimal (fun x hx => support_fderiv_subset ℝ
        (fun h0 => (Function.mem_support.mp hx) (by simp [h0])))
        (isClosed_tsupport φ)).trans hφ.sub)
  have key : ∀ v : Vr n, ∫ x, F x * fderiv ℝ φ x v = - ∫ x, fderiv ℝ F x v * φ x := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hA v) (hB v)
      (integrable_mul_of_contOn hU hF.continuousOn hφ.smooth.continuous hφ.cpt hφ.sub) hFd hφd
  have e1 : ∫ x, F x * dc a φ x
      = (∫ x, F x * fderiv ℝ φ x (v1 a.1 a.2)) + Complex.I * ∫ x, F x * fderiv ℝ φ x (v2 a.1 a.2) := by
    rw [← integral_const_mul, ← integral_add (hB _) ((hB _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  have e2 : ∫ x, dc a F x * φ x
      = (∫ x, fderiv ℝ F x (v1 a.1 a.2) * φ x) + Complex.I * ∫ x, fderiv ℝ F x (v2 a.1 a.2) * φ x := by
    rw [← integral_const_mul, ← integral_add (hA _) ((hA _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  rw [e1, e2, key, key]
  ring

theorem ibp_dList {U : Set (Vr n)} (hU : IsOpen U) :
    ∀ (l : List (Fin n × Fin n)) {F φ : Vr n → ℂ}, ContDiffOn ℝ ∞ F U → IsT U φ →
      ∫ x, F x * dList l φ x = (-1) ^ l.length * ∫ x, dList l.reverse F x * φ x := by
  intro l
  match l with
  | [] => intro F φ _ _; simp [dList]
  | a :: l =>
    intro F φ hF hφ
    have happ : ∀ (l m : List (Fin n × Fin n)) (f : Vr n → ℂ), dList (l ++ m) f = dList l (dList m f) := by
      intro l m f
      induction l with
      | nil => simp [dList]
      | cons b l ih => simp [dList, ih]
    have h1 := ibp_dc hU hF (isT_dList hφ l) a
    have h2 := ibp_dList hU l (contDiffOn_dc hU hF a) hφ
    rw [dList, h1, h2, List.reverse_cons, happ]
    simp only [dList, List.length_cons, pow_succ]
    ring

end STD

end PositivityTheory.Rg.Sw.LVs
