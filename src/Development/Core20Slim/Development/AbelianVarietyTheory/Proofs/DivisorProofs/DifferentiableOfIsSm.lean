module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Init.Data.Order.Lemmas
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
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSm_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') : IsSm σ J (f + f') :=
  fun k γ hγ g => (h k γ hγ g).add (h' k γ hγ g)

theorem isSm_smul (a : ℂ) {f : GAd σ J → ℂ} (h : IsSm σ J f) : IsSm σ J (a • f) :=
  fun k γ hγ g => (h k γ hγ g).const_smul a

theorem differentiable_of_isSm {f : GAd σ J → ℂ} (h : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (g : GAd σ J) : Differentiable ℝ fun t : ℝ => f (g * γ t) := by
  have h1 := h 1 (fun _ => γ) (fun _ => hγ) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h1.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem lineDer_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) : lineDer γ (f + f') = lineDer γ f + lineDer γ f' := by
  funext g
  exact deriv_fun_add (differentiable_of_isSm h hγ g 0) (differentiable_of_isSm h' hγ g 0)

omit [NumberField E] in
theorem lineDer_smul (a : ℂ) (f : GAd σ J → ℂ) (γ : ℝ → GAd σ J) : lineDer γ (a • f) = a • lineDer γ f := by
  funext g
  simp only [lineDer, Pi.smul_apply, smul_eq_mul, deriv_const_mul_field']

theorem isSm_lineDer {f : GAd σ J → ℂ} (hf : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSm σ J (lineDer γ f) := by
  intro k γs h g
  have h1 := hf (k + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) γs γ)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hγ
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      f (g * (List.ofFn fun i => γs i (t i)).prod * γ s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem isSm_foldr {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f : GAd σ J → ℂ}
    (hf : IsSm σ J f) : IsSm σ J (l.foldr lineDer f) := by
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    exact isSm_lineDer (ih fun δ hδ => hl δ (by simp [hδ])) (hl γ (by simp))

theorem foldr_add {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f f' : GAd σ J → ℂ}
    (hf : IsSm σ J f) (hf' : IsSm σ J f') : l.foldr lineDer (f + f') = l.foldr lineDer f + l.foldr lineDer f' := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    have hl' : ∀ δ ∈ l, IsRealLine σ J δ := fun δ hδ => hl δ (by simp [hδ])
    simp only [List.foldr_cons]
    rw [ih hl', lineDer_add (isSm_foldr hl' hf) (isSm_foldr hl' hf') (hl γ (by simp))]

omit [NumberField E] in
theorem foldr_smul (l : List (ℝ → GAd σ J)) (a : ℂ) (f : GAd σ J → ℂ) :
    l.foldr lineDer (a • f) = a • l.foldr lineDer f := by
  induction l with
  | nil => rfl
  | cons γ l ih => simp only [List.foldr_cons, ih, lineDer_smul]


end GlobalTheory.UAut

end
