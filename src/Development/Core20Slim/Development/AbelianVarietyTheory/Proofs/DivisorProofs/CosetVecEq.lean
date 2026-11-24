module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum

variable (D : D7)

def cosetV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def congLev (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : Subgroup (GA D N) :=
  Subgroup.closure {k | k ∈ intG D N ∧ CongOne D 𝔪 k}

def blockLev (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : Subgroup (GA D d) :=
  Subgroup.closure {h | h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪}

variable {D}

def stdSum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ)
    (R : Finset (GA D a)) : VC D a d → ℂ :=
  ∑ r ∈ R, W.Om r 1 (cosetV D δ 𝔪 o a d e0)

theorem congLev_le (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : congLev D 𝔪 N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem blockLev_le (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : blockLev D 𝔪 d a ≤ intG D d :=
  (Subgroup.closure_le _).2 fun _ h => h.1

end GlobalTheory.FunObj.StdDatum

end
