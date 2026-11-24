module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  first | exact @GlobalTheory.WeilCont.schA_periodic_finite_cosets | exact GlobalTheory.WeilCont.schA_periodic_finite_cosets | (intros; apply GlobalTheory.WeilCont.schA_periodic_finite_cosets <;> assumption)
