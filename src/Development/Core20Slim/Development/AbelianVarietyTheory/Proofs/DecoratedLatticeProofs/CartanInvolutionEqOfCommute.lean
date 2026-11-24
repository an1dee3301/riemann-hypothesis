module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.StdUnn

theorem isCartanInv_eq_of_commute : ∀ (k : ℕ) (G s s' : Matrix (Fin k) (Fin k) ℂ), IsCartanInv G s → IsCartanInv G s' → s * s' = s' * s → s = s' := by
  intro k G s s' h h' hc
  have key : ∀ w : Fin k → ℂ, s' *ᵥ w = -(s *ᵥ w) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := h.2.2.dotProduct_mulVec_pos hne
    have h2 := h'.2.2.dotProduct_mulVec_pos hne
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec] at h2
    exact lt_asymm h1 (neg_pos.1 h2)
  have e : s' * (1 - s * s') = -(s * (1 - s * s')) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hc, h.1,
      Matrix.mul_assoc, h'.1]
    simp
  have hr : (1 - s * s') = 0 := by
    ext i j
    have := key ((1 - s * s') *ᵥ Pi.single j 1) (by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Matrix.neg_mulVec])
    simpa using congrFun this i
  have h1 : s * s' = 1 := (sub_eq_zero.1 hr).symm
  calc s = s * (s * s') := by rw [h1, Matrix.mul_one]
    _ = s' := by rw [← Matrix.mul_assoc, h.1, Matrix.one_mul]

end GlobalTheory.StdUnn
