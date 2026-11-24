module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform

theorem symV_realLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  intro F _ _ N hF M hM t s

  let φ : InfinitePlace F → AF F →+* ℝ := fun w =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).comp
      ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)
  have hφ : ∀ w (x : AF F), φ w x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)
      (x.1 w) := fun _ _ => rfl
  have hcont : ∀ w (g : ℝ → AF F), Continuous g → Continuous fun r => φ w (g r) := by
    intro w g hg
    simp only [hφ]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal w)).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp hg))
  have lin : ∀ (p : VA F N →+ AF F), Continuous p → ∀ w r, φ w (p (M r)) = r * φ w (p (M 1)) := by
    intro p hp w r
    let f : ℝ →+ ℝ := ((φ w).toAddMonoidHom.comp p).comp M
    have hc : Continuous f := hcont w (fun r => p (M r)) (hp.comp hM.1)
    have := map_real_smul f hc r 1
    simpa [f] using this
  have p1 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_fst
  have p2 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.snd _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_snd
  have k1 : ∀ l w r, φ w ((M r).1 l) = r * φ w ((M 1).1 l) := fun l w r => lin _ (p1 l) w r
  have k2 : ∀ l w r, φ w ((M r).2 l) = r * φ w ((M 1).2 l) := fun l w r => lin _ (p2 l) w r
  have hfst : fstA F (symV (M t) (M s)) = 0 := by
    funext w
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).injective
    have h : φ w (symV (M t) (M s)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [symV, dotProduct, map_sub, map_sum, map_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [k1 l w t, k1 l w s, k2 l w t, k2 l w s]
      ring
    exact h.trans (map_zero _).symm
  have h0 : ∀ r l, sndA F ((M r).1 l) = 0 ∧ sndA F ((M r).2 l) = 0 := fun r l =>
    ⟨congrFun (hM.2 r).1 l, congrFun (hM.2 r).2 l⟩
  have hsnd : sndA F (symV (M t) (M s)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [symV, dotProduct, map_sub, map_sum, map_mul, (h0 _ _).1, (h0 _ _).2, zero_mul,
      Finset.sum_const_zero, sub_zero]
  exact Prod.ext hfst hsnd

end GlobalTheory.ThetaTransform
