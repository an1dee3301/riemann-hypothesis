module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFreeSetProjectsCompact
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_free_set_projects_compact : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ) (Q : Set (Fin (n + 1) → Fin (M + 1) → K)), IsCompact Q → (∀ Y ∈ Q, LinearIndependent K Y) → ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧ ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | exact GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails <;> assumption)
