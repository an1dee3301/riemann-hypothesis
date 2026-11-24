module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactFiniteAdeleAnnihilatorStdChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
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
theorem _root_.GlobalTheory.T.isCompact_finiteAdeleAnnihilator_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F | ∀ y ∈ L, ψ (pairA D.host.F 0 (x ⬝ᵥ y)) = 1} := by
  first | exact @GlobalTheory.AnnCompactStdChar.isCompact_annihilator_of_isStdChar | exact GlobalTheory.AnnCompactStdChar.isCompact_annihilator_of_isStdChar | (intros; apply GlobalTheory.AnnCompactStdChar.isCompact_annihilator_of_isStdChar <;> assumption)
