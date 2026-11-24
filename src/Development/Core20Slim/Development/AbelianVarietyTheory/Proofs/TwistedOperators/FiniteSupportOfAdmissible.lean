module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem adjZ_eq_neg_of_mem_upq {p q : ℕ} {Z : Mat p q} (h : Z ∈ upq p q) : adjZ Z = -Z := by
  have h0 : Zᴴ * Jm p q + Jm p q * Z = 0 := h
  have h1 : Zᴴ * Jm p q = -(Jm p q * Z) := eq_neg_of_add_eq_zero_left h0
  rw [adjZ, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc,
    GlobalTheory.InvPairingTensor.Jm_mul_self, Matrix.one_mul]

theorem finiteSupport_of_admissible :
    ∀ (p q r s : ℕ) (T : GrpData r s) (R : DSRep T), Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → FiniteSupport p q R := by
  intro p q r s T R hA A _ _ B hB P
  refine GlobalTheory.InvPairingTensor.exists_finiteDimensional_kill R hA B (fun Z hZ Q y => ?_) P
  rw [hB Z Q y, adjZ_eq_neg_of_mem_upq hZ, map_neg, LinearMap.neg_apply, map_neg, neg_add_cancel]

end GlobalTheory.Chain.IoLift
