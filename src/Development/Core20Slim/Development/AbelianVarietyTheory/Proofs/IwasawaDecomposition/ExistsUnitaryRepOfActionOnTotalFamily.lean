module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.TotalFamilyRep

variable {S H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_linearCombination_eq (E F : S → H) (h : ∀ p q, inner ℂ (F p) (F q) = inner ℂ (E p) (E q))
    (x : S →₀ ℂ) : ‖Finsupp.linearCombination ℂ F x‖ = ‖Finsupp.linearCombination ℂ E x‖ := by
  have : inner ℂ (Finsupp.linearCombination ℂ F x) (Finsupp.linearCombination ℂ F x) =
      inner ℂ (Finsupp.linearCombination ℂ E x) (Finsupp.linearCombination ℂ E x) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, h]
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Finsupp.linearCombination ℂ E x), this]

theorem exists_isometry [CompleteSpace H] (E F : S → H) (hE : Dense (Submodule.span ℂ (Set.range E) : Set H))
    (h : ∀ p q, inner ℂ (F p) (F q) = inner ℂ (E p) (E q)) :
    ∃ T : H →L[ℂ] H, (∀ x, ‖T x‖ = ‖x‖) ∧ ∀ p, T (E p) = F p := by
  have hd : DenseRange (Finsupp.linearCombination ℂ E) := by
    rw [← Finsupp.range_linearCombination] at hE
    exact hE
  have hT : ∀ x, (Finsupp.linearCombination ℂ F).extendOfNorm (Finsupp.linearCombination ℂ E)
      (Finsupp.linearCombination ℂ E x) = Finsupp.linearCombination ℂ F x :=
    LinearMap.extendOfNorm_eq hd ⟨1, fun x => by rw [one_mul, norm_linearCombination_eq E F h]⟩
  refine ⟨(Finsupp.linearCombination ℂ F).extendOfNorm (Finsupp.linearCombination ℂ E), fun x => ?_,
    fun p => ?_⟩
  · refine hd.induction_on (p := fun x => ‖(Finsupp.linearCombination ℂ F).extendOfNorm
      (Finsupp.linearCombination ℂ E) x‖ = ‖x‖) x (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_
    rw [hT, norm_linearCombination_eq E F h]
  · simpa using hT (Finsupp.single p 1)

theorem exists_rep : ∀ (G S H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (act : G → S → S) (E : S → H), (∀ p, act 1 p = p) →
    (∀ g h p, act (g * h) p = act g (act h p)) → Dense (Submodule.span ℂ (Set.range E) : Set H) →
    (∀ g p q, inner ℂ (E (act g p)) (E (act g q)) = inner ℂ (E p) (E q)) →
    (∀ p q, Continuous fun g => inner ℂ (E q) (E (act g p))) →
    ∃ π : G →* (H →L[ℂ] H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧
      ∀ g p, π g (E p) = E (act g p) := by
  intro G S H _ _ _ _ _ act E h1 hmul hE hinv hcont
  choose T hT hTE using fun g => exists_isometry E (fun p => E (act g p)) hE (hinv g)
  have hp : ∀ p, Continuous fun g => T g (E p) := by
    intro p
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have key : ∀ g, ‖T g (E p) - T g₀ (E p)‖ =
        √(‖E p‖ ^ 2 - 2 * RCLike.re (inner ℂ (E (act g₀ p)) (E (act g p))) + ‖E p‖ ^ 2) := by
      intro g
      rw [norm_sub_rev, ← hTE, ← hTE, ← Real.sqrt_sq (norm_nonneg (T g₀ (E p) - T g (E p))),
        @norm_sub_sq ℂ, hT, hT]
    have hc : Continuous fun g => ‖T g (E p) - T g₀ (E p)‖ := by
      simp only [key]
      have := hcont p (act g₀ p)
      fun_prop
    simpa using hc.tendsto g₀
  refine ⟨{ toFun := T, map_one' := ?_, map_mul' := fun g h => ?_ }, hT, ?_, hTE⟩
  · refine ContinuousLinearMap.ext_on hE ?_
    rintro _ ⟨p, rfl⟩
    simp [hTE, h1]
  · refine ContinuousLinearMap.ext_on hE ?_
    rintro _ ⟨p, rfl⟩
    simp [hTE, hmul]
  · refine GlobalTheory.FockSeq.continuous_of_dense T hT hE fun x hx => ?_
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hp p
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => simp only [map_add (f := _)]; exact hx.add hy
    | smul a x _ hx => simp only [map_smul]; exact hx.const_smul a

end GlobalTheory.TotalFamilyRep
