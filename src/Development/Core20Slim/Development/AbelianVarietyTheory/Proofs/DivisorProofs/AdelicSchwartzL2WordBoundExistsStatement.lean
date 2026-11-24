module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Classical
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_l2_word_bound_exists : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  first | exact @GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | exact GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | (intros; apply GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound <;> assumption)
