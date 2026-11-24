module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.CompanionTheory.RgEisSign

variable {k : Type} [Field k] [NumberField k]


open scoped Classical in
def even_im_hermitian_sub (ω : HeckeCharacter k) (w : {w : InfinitePlace k // w.IsReal}) : ℕ :=
  if ω.realComponent w.2 (-1) = 1 then 0 else 1

theorem realComponent_coe (ω : HeckeCharacter k) (h : IsOfFinOrder ω)
    (w : {w : InfinitePlace k // w.IsReal}) (x : ℝˣ) :
    (ω.realComponent w.2 x : ℂ) = if 0 < (x : ℝ) then (1 : ℂ) else (-1) ^ even_im_hermitian_sub ω w := by
  split_ifs with hx
  · rw [ω.realComponent_eq_one_of_isOfFinOrder h w.2 hx]; simp
  · have hneg : (x : ℝ) < 0 := lt_of_le_of_ne (not_lt.1 hx) x.ne_zero
    have hpos : 0 < ((-x : ℝˣ) : ℝ) := by simpa using hneg
    have hx' : x = (-1) * (-x) := by simp
    have hc : ω.realComponent w.2 (-1) * ω.realComponent w.2 (-1) = 1 := by
      rw [← map_mul]; simp
    rw [hx', map_mul, ω.realComponent_eq_one_of_isOfFinOrder h w.2 hpos, mul_one]
    unfold even_im_hermitian_sub
    split_ifs with h1
    · rw [h1]; simp
    · have h2 : ((ω.realComponent w.2 (-1) : Circle) : ℂ) * ((ω.realComponent w.2 (-1) : Circle) : ℂ) = 1 := by
        rw [← Circle.coe_mul, hc]; simp
      rcases mul_self_eq_one_iff.1 h2 with h3 | h3
      · exact absurd (Circle.ext (by simpa using h3)) h1
      · simpa using h3

theorem real_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsReal}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) =
      if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then (1 : ℂ)
      else (-1) ^ even_im_hermitian_sub ω w := by
  have hs := realUnitsHom_surjective w.2 (infiniteComponent w.1 a)
  have hv : ((Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 : w.1.Completion →+* ℝ).toMonoidHom
      (infiniteComponent w.1 a) : ℝˣ) : ℝ) = (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w := rfl
  rw [← hs, ← hv]
  exact realComponent_coe ω h w _

theorem complex_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsComplex}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) = 1 := by
  rw [← complexUnitsHom_surjective w.2 (infiniteComponent w.1 a)]
  have := ω.complexComponent_eq_one_of_isOfFinOrder h w.2
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 : w.1.Completion →+* ℂ).toMonoidHom
      (infiniteComponent w.1 a))
  exact congrArg (fun c : Circle => (c : ℂ)) this |>.trans (by simp)

theorem signChar : PositivityTheory.RgEis.TF.SignChar := by
  intro k _ _ ω h
  have hf : IsOfFinOrder ω :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by rw [pow_two]; exact h⟩
  refine ⟨even_im_hermitian_sub ω, fun a => ?_⟩
  rw [HeckeCharacter.toIdele_ofInfinite]
  have h1 : ((∏ w, ω.infiniteComponent w (infiniteComponent w a) : Circle) : ℂ) =
      ∏ w, (ω.infiniteComponent w (infiniteComponent w a) : ℂ) :=
    map_prod Circle.coeHom (fun w => ω.infiniteComponent w (infiniteComponent w a)) Finset.univ
  rw [h1, InfinitePlace.prod_eq_prod_mul_prod, Finset.prod_eq_one (fun w _ => complex_factor ω hf a w),
    mul_one]
  exact Finset.prod_congr rfl fun w _ => real_factor ω hf a w

end GlobalTheory.CompanionTheory.RgEisSign
