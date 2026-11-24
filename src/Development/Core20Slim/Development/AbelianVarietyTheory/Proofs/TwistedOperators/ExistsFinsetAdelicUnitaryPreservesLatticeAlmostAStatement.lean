module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostA
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsFullLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  first
  | exact @GlobalTheory.LatAlmostAll.exists_finset_keeps
  | intro F E _ _ _ _ _ σ n X hL g
    exact GlobalTheory.LatAlmostAll.exists_finset_keeps σ X hL.toIsLattice g
