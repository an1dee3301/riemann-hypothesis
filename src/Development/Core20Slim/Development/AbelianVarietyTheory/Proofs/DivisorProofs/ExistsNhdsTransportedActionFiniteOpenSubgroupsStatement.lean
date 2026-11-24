module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFiniteOpenSubgroups
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finite_openSubgroups : ∀ (D : D7) (a b : ℕ) (JA : Matrix (Fin a) (Fin a) D.host.E) (JB : Matrix (Fin b) (Fin b) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    ∀ p0 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p
          (co.e.symm (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x', GlobalTheory.WeilCont.adeleJoin D.host.F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) := by
  first | exact @GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D | exact GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D | (intros; apply GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D <;> assumption)
