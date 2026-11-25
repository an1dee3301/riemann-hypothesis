module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

theorem phase_eq_eChar (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) :
    phase w x = GlobalTheory.Published.Metaplectic.eChar (⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2) := by
  rw [GlobalTheory.Published.Metaplectic.eChar_apply, phase]
  congr 1
  push_cast
  ring

theorem hasTemperateGrowth_phase' (w : l ⊕ l → ℝ) : Function.HasTemperateGrowth (phase w) := by
  have h1 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth
  have h := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (h1.add (Function.HasTemperateGrowth.const
    (⟪pPart w, qPart w⟫ / 2)))
  have e : phase w = (GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘
      ((fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫) + fun _ => ⟪pPart w, qPart w⟫ / 2) := by
    funext x
    simp [phase_eq_eChar]
  rw [e]
  exact h

def rhoSch (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  SchwartzMap.smulLeftCLM ℂ (phase w) ∘L SchwartzMap.compSubConstCLM ℂ (-pPart w)

theorem coe_rhoSch (w : l ⊕ l → ℝ) (f : Sch l) : ⇑(rhoSch w f) = rhoFun w ⇑f := by
  funext x
  rw [rhoSch, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase' w),
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, rhoFun]

theorem exists_schwartz_rhoFun : ∀ (l : Type) [Fintype l] (w : l ⊕ l → ℝ) (f : Sch l), ∃ f₁ : Sch l, ⇑f₁ = rhoFun w ⇑f :=
  fun _ _ w f => ⟨rhoSch w f, coe_rhoSch w f⟩

end GlobalTheory.RealWeil
