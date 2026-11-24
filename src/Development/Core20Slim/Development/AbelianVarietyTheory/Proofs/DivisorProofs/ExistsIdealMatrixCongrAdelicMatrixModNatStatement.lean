module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixCongrAdelicMatrixModNat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_matrix_congr_adelicMatrix_mod_nat : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  first | exact @GlobalTheory.FunObj.CosetApprox.matrix_approx | exact GlobalTheory.FunObj.CosetApprox.matrix_approx | (intros; apply GlobalTheory.FunObj.CosetApprox.matrix_approx <;> assumption)
