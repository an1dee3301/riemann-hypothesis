module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open scoped TensorProduct

namespace GlobalTheory.UAut.ConstAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem leftInv_foldr {Γ : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (h : LeftInv Γ φ) :
    ∀ l : List (ℝ → GAd σ J), LeftInv Γ (l.foldr lineDer φ) := by
  intro l
  induction l with
  | nil => exact h
  | cons γ l ih =>
    intro x hx g
    simp only [List.foldr_cons, lineDer, mul_assoc, ih x hx]

theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have e := isRealLine_add F E σ h n J γ hγ 0 0
  rw [add_zero] at e
  exact mul_left_cancel (e.symm.trans (mul_one _).symm)

theorem hasDerivAt_foldr (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : IsSm σ J φ) {l : List (ℝ → GAd σ J)}
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun s => l.foldr lineDer φ (g * γ s)) ((γ :: l).foldr lineDer φ (g * γ t)) t := by
  have hd := (GlobalTheory.ThK.RealLineGrowthDerivative.differentiableAt_foldr_lineDer hs l hl hγ (g * γ t)).hasDerivAt
  have e : ∀ s, g * γ t * γ (s - t) = g * γ s := fun s => by
    rw [mul_assoc, ← isRealLine_add F E σ h n J γ hγ, add_sub_cancel]
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd)
  simp only [e] at h2
  exact h2

end GlobalTheory.UAut.ConstAut

end
