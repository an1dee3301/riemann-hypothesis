module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
public import Init.Core
public import Init.Data.Cast
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.SetNotation

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Count

theorem card_mul_measure_le_of_disjoint_translates :
    ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [μ.IsAddLeftInvariant] (L : AddSubgroup G) (S : Set G), MeasurableSet S → S ⊆ L →
    ∀ (ι : Type) [Fintype ι] (f : ι → G), (∀ i, f i ∈ L) →
    (∀ i j u v, u ∈ S → v ∈ S → f i + u = f j + v → i = j) →
    (Fintype.card ι : ℝ≥0∞) * μ S ≤ μ (L : Set G) := by
  intro G _ _ _ μ _ L S hS hSL ι _ f hf hdis
  let T : ι → Set G := fun i => (fun x => -f i + x) ⁻¹' S
  have hT : ∀ i, MeasurableSet (T i) := fun i => (measurable_const_add (-f i)) hS
  have hμ : ∀ i, μ (T i) = μ S := fun i => measure_preimage_add μ (-f i) S
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) T := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr ?_
    intro x hi hj
    refine hij (hdis i j (-f i + x) (-f j + x) hi hj ?_)
    simp
  have hsub : (⋃ i ∈ (Finset.univ : Finset ι), T i) ⊆ (L : Set G) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    have h1 : -f i + x ∈ L := hSL hi
    have h2 : f i + (-f i + x) ∈ L := L.add_mem (hf i) h1
    simpa using h2
  calc (Fintype.card ι : ℝ≥0∞) * μ S = ∑ i ∈ (Finset.univ : Finset ι), μ (T i) := by
        simp [hμ, Finset.card_univ]
    _ = μ (⋃ i ∈ (Finset.univ : Finset ι), T i) :=
        (measure_biUnion_finset hd (fun i _ => hT i)).symm
    _ ≤ μ (L : Set G) := measure_mono hsub

end GlobalTheory.CompanionTheory.SiegelND.Integ.Count
