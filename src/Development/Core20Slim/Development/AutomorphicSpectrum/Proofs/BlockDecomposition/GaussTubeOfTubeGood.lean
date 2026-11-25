module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def pt (x y : ℝ × ℝ) : ℂ × ℂ := (⟨x.1, y.1⟩, ⟨x.2, y.2⟩)

def dot (l : ℂ × ℂ) (t : ℝ × ℝ) : ℂ := l.1 * t.1 + l.2 * t.2

def rdot (x t : ℝ × ℝ) : ℝ := x.1 * t.1 + x.2 * t.2

def phi (G : ℂ × ℂ → X) (x t : ℝ × ℝ) : X :=
  ∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)

def inv (φ : ℝ × ℝ → X) (l : ℂ × ℂ) : X :=
  (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t

def gauss (F : ℂ × ℂ → X) (l : ℂ × ℂ) : X := Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F l

structure GaussTube (G : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol G (tube Ω)
  cont : ContinuousOn G (tube Ω)
  decay : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C,
    ‖G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))

def ExpDecay {T : Type} [TopologicalSpace T] (φ : ℝ × ℝ → T → X) : Prop :=
  ∀ (x₀ : ℝ × ℝ) (g : T), ∃ ε : ℝ, 0 < ε ∧ ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ x : ℝ × ℝ, |x.1 - x₀.1| ≤ ε → |x.2 - x₀.2| ≤ ε →
    ∀ g' ∈ U, ∀ t : ℝ × ℝ, ‖φ t g'‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))

theorem norm_exp_sq (l : ℂ × ℂ) : ‖Complex.exp (l.1 ^ 2 + l.2 ^ 2)‖ =
    Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [sq]
  ring

theorem gauss_bound {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω C : Set (ℝ × ℝ)} (h : TubeGood F Ω)
    (hC : C ⊆ Ω) (hc : IsCompact C) (g : T) : ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ l ∈ tube C,
      ‖gauss (F · g') l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  obtain ⟨U, hU, M, hM⟩ := h.bdd C hC hc g
  obtain ⟨B, hB⟩ := (hc.image (f := fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) (by fun_prop)).bddAbove
  refine ⟨U, hU, Real.exp B * |M|, fun g' hg' l hl => ?_⟩
  have h1 : l.1.re ^ 2 + l.2.re ^ 2 ≤ B := hB ⟨(l.1.re, l.2.re), hl, rfl⟩
  have h2 : ‖F l g'‖ ≤ |M| := (hM l hl g' hg').trans (le_abs_self M)
  simp only [gauss]
  rw [norm_smul, norm_exp_sq]
  have h3 : Real.exp (l.1.re ^ 2 + l.2.re ^ 2) ≤ Real.exp B := Real.exp_le_exp.2 h1
  have h4 := Real.exp_pos (-(l.1.im ^ 2 + l.2.im ^ 2))
  calc _ = Real.exp (l.1.re ^ 2 + l.2.re ^ 2) * ‖F l g'‖ * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring
    _ ≤ Real.exp B * |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by gcongr

theorem gaussTube_of_tubeGood {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (h : TubeGood F Ω) (g : T) : GaussTube (gauss (F · g)) Ω := by
  refine ⟨?_, ?_, ?_⟩
  · intro p v
    have h1 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).1 ^ 2 + (p + τ • v).2 ^ 2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      fun_prop
    exact h1.differentiableOn.smul (h.hol g p v)
  · have h1 : ContinuousOn (fun l : ℂ × ℂ => F l g) (tube Ω) :=
      h.cont.comp (f := fun l : ℂ × ℂ => (l, g)) (by fun_prop) fun l hl => ⟨hl, trivial⟩
    exact ContinuousOn.smul (by fun_prop) h1
  · intro C hC hc
    obtain ⟨U, hU, M, hM⟩ := gauss_bound h hC hc g
    exact ⟨M, fun l hl => hM g (mem_of_mem_nhds hU) l hl⟩

end GlobalTheory.CompanionTheory.TubeFourier
