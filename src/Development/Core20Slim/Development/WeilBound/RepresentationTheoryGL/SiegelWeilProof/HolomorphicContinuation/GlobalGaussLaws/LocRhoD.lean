module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoC
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem dirAt_ne {m : ℕ} {τ τ' : D.what₂.Tau} (h : τ' ≠ τ) (Z : Matrix (Fin m) (Fin n) ℂ) :
    GlobalTheory.FockAnnKill.dirAt τ Z τ' = 0 := by
  exact if_neg h

theorem dirAt_self {m : ℕ} (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin n) ℂ) : GlobalTheory.FockAnnKill.dirAt τ Z τ = Z := by
  exact if_pos rfl

theorem gAway_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin n) ℂ) : gAway V l s τ (GlobalTheory.FockAnnKill.dirAt τ Z) = 1 := by
  classical
  show Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ τ' with τ' ≠ τ, ((|l τ'| : ℝ) : ℂ) *
      ((GlobalTheory.FockAnnKill.dirAt τ Z τ').conjTranspose * (Formalism.BasicNotions.TH.gramAt D V τ' * s τ') *
        GlobalTheory.FockAnnKill.dirAt τ Z τ').trace) = 1
  rw [Finset.sum_eq_zero fun τ' hτ' => by rw [dirAt_ne (Finset.mem_filter.mp hτ').2 Z]; simp,
    mul_zero, Complex.exp_zero]

theorem trace_conjTranspose_mul_self {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (uᴴ * u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_mul']
  push_cast
  exact Finset.sum_comm

theorem gauss_dirAt {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (l : D.what₂.Tau → ℝ) (u : Matrix (Fin V.rank) (Fin n) ℂ) :
    gauss V l s (GlobalTheory.FockAnnKill.dirAt τ (fr * u)) = gs (cLoc l τ) u := by
  show Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ τ', ((|l τ'| : ℝ) : ℂ) *
      ((GlobalTheory.FockAnnKill.dirAt τ (fr * u) τ').conjTranspose * (Formalism.BasicNotions.TH.gramAt D V τ' * s τ') *
        GlobalTheory.FockAnnKill.dirAt τ (fr * u) τ').trace) =
    Complex.exp (-(((2 * Real.pi * |l τ|) * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ))
  have key : (fr * u)ᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * (fr * u) = uᴴ * u := by
    rw [Matrix.conjTranspose_mul,
      show uᴴ * frᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * (fr * u) =
        uᴴ * (frᴴ * (Formalism.BasicNotions.TH.gramAt D V τ * s τ) * fr) * u by simp only [Matrix.mul_assoc],
      hfr.2.2, Matrix.mul_one]
  rw [Finset.sum_eq_single τ (fun τ' _ h => by rw [dirAt_ne h]; simp)
      (fun h => absurd (Finset.mem_univ τ) h), dirAt_self, key, trace_conjTranspose_mul_self]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
