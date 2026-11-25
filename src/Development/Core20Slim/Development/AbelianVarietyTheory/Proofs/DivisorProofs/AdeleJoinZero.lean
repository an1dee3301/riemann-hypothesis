module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Classical
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal Classical

namespace GlobalTheory.WeilL2Words

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def arch1 (z : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0)

def IsStdInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∃ ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ, (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) ∧
    ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)

def arch (x : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F := fun i => arch1 F (x i)

def archPair (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) :=
  (arch F h.1, arch F h.2)

def archPart (a : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

def l2A (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℝ≥0∞ :=
  @lintegral _ (borel _) μ fun y => ∫⁻ x, ‖Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

def dS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun a => deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0

def word (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  hs.foldr (fun h g => dS F ψ h g) Φ

theorem word_cons (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h) (hs) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ (h :: hs) Φ = dS F ψ h (word F ψ hs Φ) := rfl

end GlobalTheory.WeilL2Words

end
