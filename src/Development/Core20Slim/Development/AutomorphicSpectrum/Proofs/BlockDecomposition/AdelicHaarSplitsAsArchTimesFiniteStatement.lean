module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFinite
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_splits_as_arch_times_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure →
  ∃ (μ₁ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (μ₂ : Measure (Fin n → Fin M → Af F ⊗[F] E)) (c : ℝ≥0∞),
    μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ SFinite μ₁ ∧ SFinite μ₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    dx.map (fun X => (projInf X, projFin X)) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | exact GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple <;> assumption)
