module

public import Mathlib
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core

open NumberField IsDedekindDomain MeasureTheory Matrix Topology
open scoped ENNReal NNReal MatrixGroups

section Abstract

def SB {V : Type} [TopologicalSpace V] (φ : V → ℂ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ

def perp {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}

def NADual (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ)
    (μ : Measure V) : Prop :=
  IsTopologicalAddGroup V ∧ T2Space V ∧ LocallyCompactSpace V ∧ SecondCountableTopology V ∧ BorelSpace V ∧
    μ.IsAddHaarMeasure ∧
    (∀ U ∈ 𝓝 (0 : V), ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ (L : Set V) ⊆ U) ∧
    (∀ x : V, ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ x ∈ L) ∧
    Continuous (fun p : V × V => χ p.1 p.2) ∧ (∀ x y, χ x y = χ y x) ∧ (∀ x y, ‖χ x y‖ = 1) ∧
    (∀ x x' y, χ (x + x') y = χ x y * χ x' y) ∧
    ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) →
      IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1

def fou {V : Type} [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V) (φ : V → ℂ) (y : V) : ℂ :=
  ∫ x, φ x * χ x y ∂μ

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]

def chiB (ψ : AddChar R ℂ) (B : Matrix ι ι R) (x y : ι → R) : ℂ := ψ (x ⬝ᵥ (B *ᵥ y))

def qf (h : R) (B : Matrix ι ι R) (x : ι → R) : R := h * (x ⬝ᵥ (B *ᵥ x))

def Heisenberg₂ (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (x y : ι → R) (φ : (ι → R) → ℂ) (u : ι → R) : ℂ :=
  ψ (u ⬝ᵥ (B *ᵥ y) + h * (x ⬝ᵥ (B *ᵥ y))) * φ (u + x)

def opU (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (b : R) (φ : (ι → R) → ℂ) (u : ι → R) : ℂ :=
  ψ (b * qf h B u) * φ u

def opD (m : ℝ) (a : R) (φ : (ι → R) → ℂ) (u : ι → R) : ℂ := (m : ℂ) * φ (a • u)

def nMat (b : R) : SL(2, R) := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

def mMat (a : Rˣ) : SL(2, R) := ⟨!![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)], by simp [Matrix.det_fin_two]⟩

def wMat : SL(2, R) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

variable [TopologicalSpace R] [MeasurableSpace R]

def Impl (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)) (g : SL(2, R))
    (T : ((ι → R) → ℂ) → ((ι → R) → ℂ)) : Prop :=
  (∀ φ, SB φ → SB (T φ)) ∧ (∀ φ', SB φ' → ∃ φ, SB φ ∧ T φ = φ') ∧
    (∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ') ∧ (∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) ∧
    (∀ φ, SB φ → ∫ u, ‖T φ u‖ ^ 2 ∂μ = ∫ u, ‖φ u‖ ^ 2 ∂μ) ∧
    ∀ x y φ, SB φ → Heisenberg₂ ψ h B x y (T φ) =
      T (Heisenberg₂ ψ h B (g 0 0 • x + g 1 0 • y) (g 0 1 • x + g 1 1 • y) φ)

def NAQuad (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)) : Prop :=
  IsTopologicalRing R ∧ 2 * h = 1 ∧ Continuous ψ ∧ (∀ r, ‖ψ r‖ = 1) ∧ B.IsSymm ∧
    NADual (ι → R) (chiB ψ B) μ

def fstar (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)) (φ : (ι → R) → ℂ) (b : R) : ℂ :=
  ∫ u, opU ψ h B b φ u ∂μ

end Abstract

section Global

variable (F : Type) [Field F] [NumberField F]

abbrev A := FiniteAdeleRing (𝓞 F) F

def Oh : Set (A F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}

def kap : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹

def hf : A F := algebraMap F (A F) (1 / 2)

def IsStdChar (ψ : AddChar (A F) ℂ) : Prop :=
  Continuous ψ ∧ ∀ b : F, ψ (algebraMap F (A F) b) =
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ))

variable {F}

def den (b : F) : ℕ :=
  Ideal.absNorm (Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F b) (1 : Submodule (𝓞 F) F))

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def QSetup (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) : Prop :=
  IsTotallyReal F ∧ Fintype.card ι = 2 * M ∧ B.IsSymm ∧ B.det ≠ 0 ∧
    (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) ∧ (∀ w, (P w).PosDef) ∧
    ∀ w, P w * (B.map (ρ w))⁻¹ * P w = B.map (ρ w)

def Bf (B : Matrix ι ι F) : Matrix ι ι (A F) := B.map (algebraMap F (A F))

def muF [MeasurableSpace (A F)] (B : Matrix ι ι F) (lf : Measure (A F)) : Measure (ι → A F) :=
  ENNReal.ofReal (kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹) •
    Measure.pi fun _ => lf

def gauss (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ) : ℂ :=
  Complex.exp (∑ w, ((Real.pi : ℂ) * Complex.I * ((τ w).re : ℂ) * ((x w ⬝ᵥ (B.map (ρ w) *ᵥ x w) : ℝ) : ℂ) -
    (Real.pi : ℂ) * ((τ w).im : ℂ) * ((x w ⬝ᵥ (P w *ᵥ x w) : ℝ) : ℂ)))

def cG (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) : ℂ :=
  (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) * ∫ x, gauss B ρ P τ x

def thTerm (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) (x : ι → F) : ℂ :=
  φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) * gauss B ρ P τ (fun w => gi w *ᵥ fun j => ρ w (x j))

def theta (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) : ℂ :=
  ∑' x : ι → F, thTerm B ρ P gf gi φ τ x

def IsOrth (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (gf : Matrix ι ι (A F))
    (gi : InfinitePlace F → Matrix ι ι ℝ) : Prop :=
  gfᵀ * Bf B * gf = Bf B ∧ ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)

def eiTerm [MeasurableSpace (A F)] (ψ : AddChar (A F) ℂ) (lf : Measure (A F)) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) (b : F) : ℂ :=
  fstar ψ (hf F) (Bf B) (muF B lf) φ (algebraMap F (A F) b) * cG B ρ P (fun w => τ w + (ρ w b : ℝ))

def eis [MeasurableSpace (A F)] (ψ : AddChar (A F) ℂ) (lf : Measure (A F)) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) : ℂ :=
  φ 0 + ∑' b : F, eiTerm ψ lf B ρ P φ τ b

def wt (M : ℕ) (τ : InfinitePlace F → ℂ) : ℝ := ∏ w, Real.sqrt (τ w).im ^ M

def mob (ρ : InfinitePlace F → (F →+* ℝ)) (γ : SL(2, F)) (τ : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun w => ((ρ w (γ 0 0) : ℝ) * τ w + (ρ w (γ 0 1) : ℝ)) / ((ρ w (γ 1 0) : ℝ) * τ w + (ρ w (γ 1 1) : ℝ))

def cnt (ρ : InfinitePlace F → (F →+* ℝ)) (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ)
    (N : ℕ) (R : ℝ) : ℝ≥0∞ :=
  ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F |
    (∀ i v, ((N : A F) * (gf *ᵥ fun j => algebraMap F (A F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧
      ∀ w, ‖gi w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1

def CountData [MeasurableSpace (A F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F))
    (gi : Ω → InfinitePlace F → Matrix ι ι ℝ) : Prop :=
  IsProbabilityMeasure Pr ∧ (∀ w i j, Measurable fun ω => gi ω w i j) ∧ (∀ i j, Measurable fun ω => gf ω i j) ∧
    (∀ ω, IsOrth B ρ (gf ω) (gi ω)) ∧
    ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, cnt ρ (gf ω) (gi ω) N R ∂Pr ≤
      ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))

def indL (a : ℕ) : (ι → A F) → ℂ :=
  Set.indicator {x | ∀ i, (a : A F) * x i ∈ Oh F} fun _ => 1

def latR (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) : AddSubgroup (InfinitePlace F → ℝ) :=
  AddSubgroup.closure {y | ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))}

end Global

end GlobalTheory.CompanionTheory.SW.Core
