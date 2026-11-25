module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GodementSection
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMG

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

variable {k : Type} [Field k] [NumberField k]

theorem lineZeta_ratV_unit (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (ξ : Unit → k) (hξ : ξ ≠ 0) : lineZeta Ψ₁ ω z (ratV ξ) = tate Ψ₁ ω z := by
  have h0 : ξ () ≠ 0 := fun h => hξ (funext fun i => by cases i; exact h)
  haveI := isHaarMeasure_ideleMeasure k
  haveI := IdeleGroup.borelSpace k
  have key := integral_mul_left_eq_self (μ := ideleMeasure k)
    (fun x : IdeleGroup k => Ψ₁ (fun _ => (x : 𝔸[k])) * ((ω.toIdele x : Circle) : ℂ) *
      ((((IdeleGroup.ideleModule k x : {r : ℝ // 0 < r}) : ℝ) : ℂ) ^ z))
    (IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0))
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ((x : 𝔸[k]) • ratV ξ) =
      fun _ => ((IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0) * x : IdeleGroup k) : 𝔸[k]) := by
    funext i
    cases i
    simp [ratV, IdeleGroup.diagonal, mul_comm]
  simp only [hx, map_mul, HeckeCharacter.toIdele_diagonal, IdeleGroup.ideleModule_diagonal, one_mul]

theorem proj_unit_eq (l l' : Projectivization k (Unit → k)) : l = l' := by
  induction l using Projectivization.ind
  rename_i v hv
  induction l' using Projectivization.ind
  rename_i w hw
  rw [Projectivization.mk_eq_mk_iff']
  have hw0 : w () ≠ 0 := fun h => hw (funext fun i => by cases i; exact h)
  exact ⟨v () / w (), funext fun i => by cases i; simp [div_mul_cancel₀ _ hw0]⟩

theorem epstein_unit_one (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) :
    epstein Ψ₁ ω z 1 = tate Ψ₁ ω z := by
  have hne : (fun _ : Unit => (1 : k)) ≠ 0 := fun h => one_ne_zero (congrFun h ())
  unfold epstein
  rw [tsum_eq_single (Projectivization.mk k (fun _ : Unit => (1 : k)) hne)
    (fun b hb => absurd (proj_unit_eq b _) hb)]
  simp only [inv_one, Units.val_one, Matrix.one_mulVec]
  exact lineZeta_ratV_unit Ψ₁ ω z _ (Projectivization.rep_nonzero _)

theorem zetaOne_of_epMain : EpMain → ZetaOne := by
  intro h
  unfold EpMain at h
  unfold ZetaOne
  intro k _ _ Ψ₁ ω hΨ hω
  obtain ⟨V, -, hV⟩ := h k
  obtain ⟨F, F', hF, -, -, -⟩ := hV Unit Ψ₁ ω hΨ hω
  refine ⟨fun z => F z 1, ?_, fun z hz => ?_⟩
  · unfold PolyEnt
    refine ⟨hF.entire 1, fun b c => ?_⟩
    obtain ⟨M, hM⟩ := hF.strip b c {1} isCompact_singleton
    exact ⟨M, fun z h1 h2 => hM z h1 h2 1 rfl⟩
  · show F z 1 = _
    rw [hF.eq z (by simpa using hz) 1, epstein_unit_one]
    simp

end GlobalTheory.CompanionTheory.EisMG
