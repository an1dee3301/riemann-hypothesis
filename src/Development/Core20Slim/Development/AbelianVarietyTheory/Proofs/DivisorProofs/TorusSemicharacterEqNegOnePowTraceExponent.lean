module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem sig_eq_star (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := by
  have τ0 : D.what₂.Tau := D.eTau.symm 1
  apply (tauE D τ0).injective
  rw [GlobalTheory.FockCompare.tauE_star]
  exact D.sp.cm.cmUnram.2.1 (tauE D τ0) x

theorem cT_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
  refine Matrix.ext fun i j => ?_
  simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (A j i) = star (A j i)
  exact sig_eq_star _

theorem hRat_eq (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T x y = Matrix.trace (S.gram⁻¹ * yᴴ * T.gram * x) := by
  simp only [GlobalTheory.LatVac.hRat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem hRat_frames (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1)
    (hB' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)
      (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = Matrix.trace (Mᴴ * M) := by
  rw [cT_eq] at hB hB'
  rw [hRat_eq]
  set Bi := (B⁻¹ : GL (Fin S.rank) D.host.E).1 with hBi_def
  have hBi : Bi * B.1 = 1 := by rw [hBi_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSi : S.gram⁻¹ = B.1 * B.1ᴴ := by
    have h1 : B.1 * (B.1ᴴ * S.gram) = 1 := mul_eq_one_comm.1 hB
    have h2 : (B.1 * B.1ᴴ) * S.gram = 1 := by rw [Matrix.mul_assoc]; exact h1
    exact Matrix.inv_eq_left_inv h2
  have hBB : B.1ᴴ * Biᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  calc Matrix.trace (S.gram⁻¹ * (B'.1 * M * Bi)ᴴ * T.gram * (B'.1 * M * Bi))
      = Matrix.trace (B.1 * ((B.1ᴴ * Biᴴ) * (Mᴴ * ((B'.1ᴴ * T.gram * B'.1) * (M * Bi))))) := by
        rw [hSi]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (B.1 * (Mᴴ * (M * Bi))) := by rw [hBB, hB', Matrix.one_mul, Matrix.one_mul]
    _ = Matrix.trace ((Mᴴ * M * Bi) * B.1) := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Mᴴ * M) := by rw [Matrix.mul_assoc, hBi, Matrix.mul_one]




end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}




end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}



end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}



end GlobalTheory.SemicharTrace
