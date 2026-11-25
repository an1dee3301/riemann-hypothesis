module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix

namespace GlobalTheory.RealWeil

theorem tendsto_slope_omS_schwartz :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] (pr : G →* Matrix.symplecticGroup l ℝ)
    (om : G →* (GlobalTheory.RealWeil.L2 l ≃ₗᵢ[ℂ] GlobalTheory.RealWeil.L2 l)) (omS : G →* (GlobalTheory.RealWeil.Sch l →L[ℂ] GlobalTheory.RealWeil.Sch l)),
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : GlobalTheory.RealWeil.L2 l),
      om g (GlobalTheory.RealWeil.rho w f) = GlobalTheory.RealWeil.rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) →
    (∀ (g : G) (f : GlobalTheory.RealWeil.Sch l), om g (f.toLp 2) = (omS g f).toLp 2) →
    ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
    (∀ f : GlobalTheory.RealWeil.Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((GlobalTheory.RealWeil.quad X f).toLp 2) 0) →
    ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (omS (γ t) f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (GlobalTheory.RealWeil.quad X f)) := by
  intro l _ _ G _ pr om omS h3 h4 X hX γ h0 hγ h6 f
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have key : ∀ r, Filter.Tendsto
      (fun t : ℝ => ‖schwartzToL2 l (A r (t⁻¹ • (omS (γ t) f - f) - quad X f))‖) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro r
    have h := hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_toLp_omS h3 h4 hX h0 hγ h6 (hA r) f)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    refine h.congr fun t => ?_
    have e : ∀ (B : Sch l →L[ℂ] L2 l) (u v w : Sch l) (s : ℝ), B (s • (u - v) - w) = s • (B u - B v) - B w := by
      intro B u v w s
      rw [B.map_sub, B.map_smul_of_tower, B.map_sub]
    have e1 : omS (γ 0) f = f := by rw [h0, omS.map_one]; rfl
    rw [zero_add, e1]
    exact congrArg norm (e ((schwartzToL2 l).comp (A r)) _ _ _ _).symm
  have hs := tendsto_finsetSum Finset.univ fun r _ => key r
  rw [Finset.sum_const_zero] at hs
  filter_upwards [hs.eventually (gt_mem_nhds hε)] with t ht
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  exact (hb _).trans_lt ht

end GlobalTheory.RealWeil
