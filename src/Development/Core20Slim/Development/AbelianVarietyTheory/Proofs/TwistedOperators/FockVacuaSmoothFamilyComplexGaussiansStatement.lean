module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussians
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_smooth_family_complexGaussians : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.FockFamily.fock_vacua_family | exact GlobalTheory.FockFamily.fock_vacua_family | (intros; apply GlobalTheory.FockFamily.fock_vacua_family <;> assumption)
