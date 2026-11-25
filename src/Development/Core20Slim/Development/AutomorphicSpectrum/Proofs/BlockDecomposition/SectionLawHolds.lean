module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Iwa
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Restrict
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisSec

variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem isQuotientMap_mul [IsTopologicalGroup G] {K P : Subgroup G} (hK : IsCompact (K : Set G))
    (hP : IsClosed (P : Set G)) (hI : Iwa P K) :
    Topology.IsQuotientMap (fun x : P × K => (x.1 : G) * (x.2 : G)) :=
  _root_.UpperTheory.Reformulated.B.DYhc7.main hK hP hI

theorem sec_mul {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} (hch : IsCh Γ P c)
    {w : W} (hw : w ∈ secSp K P c ρ) {p : G} (hp : p ∈ P) (k : K) :
    sec K P c ρ (p * k) w = c p • ρ k⁻¹ w := by
  have h : ∃ k' : K, (p * (k : G)) * (k' : G)⁻¹ ∈ P := ⟨k, by simpa using hp⟩
  rw [sec, dite_eq_left h]
  obtain ⟨k0, hk0⟩ : ∃ k0 : K, k0 = h.choose := ⟨_, rfl⟩
  have h0 : p * (k : G) * (k0 : G)⁻¹ ∈ P := hk0 ▸ h.choose_spec
  rw [← hk0]
  have hr : ((k0 * k⁻¹ : K) : G) ∈ P := by
    have : ((k0 * k⁻¹ : K) : G) = (p * (k : G) * (k0 : G)⁻¹)⁻¹ * p := by simp [mul_assoc]
    rw [this]
    exact P.mul_mem (P.inv_mem h0) hp
  have hrw : c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w = w := hw _ hr
  have hcp : c p = c (p * (k : G) * (k0 : G)⁻¹) * c ((k0 * k⁻¹ : K) : G) := by
    rw [← hch.mul _ h0 _ hr]
    congr 1
    simp [mul_assoc]
  have hρ : ρ k⁻¹ = ρ k0⁻¹ * ρ (k0 * k⁻¹) := by
    rw [← map_mul]
    congr 1
    simp
  calc (c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹) w
      = c (p * (k : G) * (k0 : G)⁻¹) • ρ k0⁻¹ (c ((k0 * k⁻¹ : K) : G) • ρ (k0 * k⁻¹) w) := by
        rw [hrw]; rfl
    _ = c p • ρ k⁻¹ w := by
        rw [hcp, hρ, map_smul, mul_smul]; rfl

theorem sec_continuous [IsTopologicalGroup G] {Γ K P : Subgroup G} {c : G → ℂ}
    {ρ : K →* (W →L[ℂ] W)} (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c)
    {w : W} (hw : w ∈ secSp K P c ρ) : Continuous fun g => sec K P c ρ g w := by
  refine (isQuotientMap_mul hK hpar.closed hpar.iwa).continuous_iff.mpr ?_
  have hc : Continuous fun p : P => c p := continuousOn_iff_continuous_restrict.mp hpar.ch.cont
  have he : ((fun g => sec K P c ρ g w) ∘ fun x : P × K => (x.1 : G) * (x.2 : G))
      = fun x : P × K => c x.1 • ρ x.2⁻¹ w := by
    funext x
    exact sec_mul hpar.ch hw x.1.2 x.2
  rw [he]
  have h2 : Continuous fun k : K => ρ k⁻¹ w :=
    (hρ.comp continuous_inv).clm_apply continuous_const
  exact (hc.comp continuous_fst).smul (h2.comp continuous_snd)

theorem sec_bound {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)}
    (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c) :
    ∃ M : ℝ, ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hρ).isBounded.exists_norm_le
  refine ⟨M, fun g w => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hpar.iwa g
  have h : ∃ k' : K, (p * k) * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [sec, dite_eq_left h, ContinuousLinearMap.smul_apply, norm_smul, hpar.ch.norm _ h.choose_spec,
    one_mul]
  exact ((ρ _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM _ ⟨_, rfl⟩) (norm_nonneg _))

theorem secLaw : SecLaw := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P c hpar
  exact ⟨fun w hw p hp k => sec_mul hpar.ch hw hp k,
    fun w hw => sec_continuous hK hρ hpar hw, sec_bound hK hρ hpar⟩

end GlobalTheory.CompanionTheory.RgEisSec
