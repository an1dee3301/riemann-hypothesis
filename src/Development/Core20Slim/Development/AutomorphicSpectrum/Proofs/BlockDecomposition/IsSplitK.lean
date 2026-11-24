module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

section Gen

variable {V H : Type} [MeasurableSpace V] [MeasurableSpace H]

def DenLE (μ : Measure V) (ν : Measure H) (q : V → H) (S : Set V) (C : ℝ≥0∞) : Prop :=
  ∀ Y, MeasurableSet Y → μ (S ∩ q ⁻¹' Y) ≤ C * ν Y

end Gen

section Box

variable {K W : Type} [CommRing K] [Fintype W] {n M : ℕ}

def boxK (κ : K ≃+* (W → ℂ)) (r : Fin n → W → ℝ) : Set (Fin n → Fin M → K) :=
  {X | ∀ a i w, ‖κ (X a i) w‖ ≤ r a w}

def nearK (κ : K ≃+* (W → ℂ)) (w : W) (s : Fin n → ℂ) (ε : ℝ) : Set (Fin n → Fin M → K) :=
  {X | ∀ i, ‖∑ b, s b * κ (X b i) w‖ < ε}

def goodK (κ : K ≃+* (W → ℂ)) (R ε : ℝ) : Set (Fin n → Fin M → K) :=
  boxK κ (fun _ _ => R) \ ⋃ w : W, ⋃ a : Fin n, ⋃ s ∈ {s : Fin n → ℂ | s a = 1 ∧ ∀ b, ‖s b‖ ≤ 1}, nearK κ w s ε

def shearK (a : Fin n) (s : Fin n → K) (X : Fin n → Fin M → K) : Fin n → Fin M → K :=
  Function.update X a (fun i => X a i + ∑ b, s b * X b i)

def shearM (a : Fin n) (s : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 + Matrix.of fun b c => if c = a then s b else 0

end Box

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsSplitK (e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ)) (σ : E →ₐ[F] E)
    (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph κ ∧ (∀ x w, κ (sigR (Ainf F) σ x) w = (starRingEnd ℂ) (κ x w)) ∧
    ∀ a w, κ (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) w = (e a w : ℂ)

end Split

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
