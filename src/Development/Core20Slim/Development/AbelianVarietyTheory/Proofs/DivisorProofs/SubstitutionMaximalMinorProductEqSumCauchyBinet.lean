module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormRowSubProdMinors
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem substF_minorPol_eq_sum : ∀ (D : D7) {a d : ℕ} {m : D.what₂.Tau → ℕ} (K : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ)
    (T : Tup D a d m), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (minorPol D T) =
      ∑ T' : Tup D a d m, (∏ τ, ∏ r, (Matrix.of fun i i' : Fin a => K τ ((T' τ r).1 i') ((T τ r).1 i)).det) •
        minorPol D T' := by
  intro D a d m K T
  have hmin : ∀ τ (s : Fin a → Fin d), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))
      (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det =
      ∑ s' : {s : Fin a → Fin d // StrictMono s},
        MvPolynomial.C ((Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)).det) *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s'.1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det]
    have hM : (GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))).mapMatrix
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
        (Matrix.of fun (i : Fin a) (k : Fin d) => (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) *
        (Matrix.of fun (k : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, k, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) := by
      refine Matrix.ext fun i i' => ?_
      simp only [RingHom.mapMatrix_apply, AlgHom.coe_toRingHom, Matrix.map_apply, Matrix.of_apply,
        GlobalTheory.CompactHowe.substF_X, Matrix.mul_apply, Matrix.one_apply]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single i']
      · simp
      · intro l _ hl; simp [Matrix.one_apply_ne hl]
      · simp
    rw [hM, GlobalTheory.MinorFrame.det_mul_eq_sum_sm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    congr 1
    rw [show (Matrix.of fun (i : Fin a) (k : Fin d) =>
        (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).submatrix id s'.1 =
        (MvPolynomial.C : ℂ →+* MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ).mapMatrix
          (Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)) from by ext; simp]
    rw [← RingHom.map_det]
  unfold minorPol
  simp only [map_prod, hmin]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [← MvPolynomial.C_mul']
  simp only [Finset.prod_mul_distrib, map_prod]

end GlobalTheory.NormDict
