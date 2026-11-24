module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Monotone.Defs

@[expose] public section

open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
