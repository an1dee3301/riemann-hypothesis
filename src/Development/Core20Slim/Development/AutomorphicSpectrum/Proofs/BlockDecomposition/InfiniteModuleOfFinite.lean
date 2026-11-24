module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ConductorIdeal
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Prop
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.EisTestFun

variable {k : Type} [Field k] [NumberField k]

theorem infiniteModule_ofFinite (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    infiniteModule (ofFinite b) = 1 := by
  have h : ((ofFinite b : IdeleGroup k) : AdeleRing (𝓞 k) k).1 = (1 : AdeleRing (𝓞 k) k).1 := rfl
  unfold infiniteModule
  refine Finset.prod_eq_one fun w _ => ?_
  rw [h, adele_fst_one_apply, norm_one, one_pow]

theorem ideleModule_ofFinite (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    (ideleModule k (ofFinite b) : ℝ) = finiteModule (ofFinite b) := by
  rw [ideleModule_apply, infiniteModule_ofFinite, one_mul]

theorem line_lc_cs {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hg : g ∈ GJMatrix.finiteSchwartzBruhatPi k) :
    IsLocallyConstant (fun t : FiniteAdeleRing (𝓞 k) k => g fun _ => t) ∧
      HasCompactSupport (fun t : FiniteAdeleRing (𝓞 k) k => g fun _ => t) := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨hlc.comp_continuous (continuous_pi fun _ => continuous_id), ?_⟩
  exact hcs.comp_homeomorph (Homeomorph.funUnique Unit (FiniteAdeleRing (𝓞 k) k)).symm

theorem zFinPos : ZFinPos := by
  intro K _ _ g hg hnn h1 x hx
  haveI := isHaarMeasure_finiteIdeleMeasure K
  obtain ⟨hlc, hcs⟩ := line_lc_cs hg
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hcs.isCompact
  obtain ⟨B, hB⟩ := hlc.continuous.bounded_above_of_compact_support hcs
  let G : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ := fun b => (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)).re
  let F : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ := fun b => G b * finiteZetaBound L x b
  have hG0 : ∀ b, 0 ≤ G b := by
    intro b
    obtain ⟨r, hr, hgr⟩ := hnn (b : FiniteAdeleRing (𝓞 K) K)
    simp only [G, hgr, Complex.ofReal_re]
    exact hr
  have hGc : Continuous G :=
    Complex.continuous_re.comp (hlc.continuous.comp Units.continuous_val)
  have hGB : ∀ b, ‖G b‖ ≤ B := by
    intro b
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hB _)
  have hint : Integrable F (finiteIdeleMeasure K) :=
    (integrable_finiteZetaBound L hx).bdd_mul hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall hGB)
  have hF0 : 0 ≤ F := fun b => mul_nonneg (hG0 b) (finiteZetaBound_nonneg L x b)
  have hzero : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (b : FiniteAdeleRing (𝓞 K) K) ∉ idealFiniteAdeles L →
        (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = 0 := by
    intro b hb
    by_contra hne
    exact hb (hL (subset_tsupport _ hne))
  have heq : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) * ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) *
        ((ideleModule K (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((F b : ℝ) : ℂ) := by
    intro b
    have hc : ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) = 1 := by
      rw [HeckeCharacter.toIdele_apply]
      rfl
    rw [hc, mul_one, ideleModule_ofFinite]
    simp only [F, G, finiteZetaBound]
    split_ifs with hb
    · obtain ⟨r, hr, hgr⟩ := hnn (b : FiniteAdeleRing (𝓞 K) K)
      rw [hgr, Complex.ofReal_re, Complex.ofReal_mul,
        Complex.ofReal_cpow (finiteModule_pos _).le]
    · rw [hzero b hb]
      simp
  have hI : zFin g 1 (x : ℂ) = ((∫ b, F b ∂finiteIdeleMeasure K : ℝ) : ℂ) := by
    unfold zFin
    exact (integral_congr_ae (Filter.Eventually.of_forall heq)).trans integral_complex_ofReal
  let U : Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    {b | (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1}
  have hUo : IsOpen U := (hlc.comp_continuous Units.continuous_val).isOpen_fiber _
  have h1U : (1 : (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ U := by
    show (g fun _ => ((1 : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1
    rw [Units.val_one]
  obtain ⟨r, hr, hgr⟩ := hnn 1
  have hr0 : 0 < r := by
    refine lt_of_le_of_ne hr ?_
    rintro rfl
    exact h1 (by rw [hgr, Complex.ofReal_zero])
  have hUsub : U ⊆ Function.support F := by
    intro b hb
    have hgb : (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = r := (show _ = _ from hb).trans hgr
    have hmem : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L := by
      by_contra hn
      have h0 := hzero b hn
      rw [hgb] at h0
      exact hr0.ne' (by exact_mod_cast h0)
    rw [Function.mem_support]
    simp only [F, G, finiteZetaBound, if_pos hmem, hgb, Complex.ofReal_re]
    exact (mul_pos hr0 (Real.rpow_pos_of_pos (finiteModule_pos _) _)).ne'
  have hpos : 0 < finiteIdeleMeasure K (Function.support F) :=
    (hUo.measure_pos _ ⟨1, h1U⟩).trans_le (measure_mono hUsub)
  rw [hI, Complex.ofReal_ne_zero]
  exact ((integral_pos_iff_support_of_nonneg hF0 hint).2 hpos).ne'

end GlobalTheory.CompanionTheory.EisTestFun
