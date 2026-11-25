module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HRatFrame

theorem trace_conjTranspose_mul_self_sum {R : Type*} [CommRing R] [StarRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    Matrix.trace (Aᴴ * A) = ∑ a, ∑ b, star (A a b) * A a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem hRat_frame : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.LatVac.hRat S T v v = ∑ a, ∑ b, star (((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b) * ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b := by
  intro D S T frS frT hS hT v
  have hT2 : frT.1 * (frT⁻¹ : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hS2 : frS.1 * (frS⁻¹ : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hv : frT.1 * ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) * (frS⁻¹ : GL (Fin S.rank) D.host.E).1 = v := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hS2, Matrix.mul_one, ← Matrix.mul_assoc, hT2, Matrix.one_mul]
  have key := GlobalTheory.SemicharTrace.hRat_frames S T frS frT hS hT ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1)
  rw [hv] at key
  rw [key, trace_conjTranspose_mul_self_sum]

end GlobalTheory.HRatFrame
