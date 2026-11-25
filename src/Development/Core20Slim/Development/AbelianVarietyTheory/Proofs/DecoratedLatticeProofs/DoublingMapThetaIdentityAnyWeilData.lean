module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardCharStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNegStatement
public import Batteries.Logic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.DoublingTheta

section Matrices

variable (R : Type) [CommRing R] (m n : ℕ)

def inL : Matrix (Fin (m + n)) (Fin m) R :=
  (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin n) (Fin m) R)).submatrix finSumFinEquiv.symm id

def inR : Matrix (Fin (m + n)) (Fin n) R :=
  (Matrix.fromRows (0 : Matrix (Fin m) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)).submatrix finSumFinEquiv.symm id

variable {R m n}

theorem inL_map {R' : Type} [CommRing R'] (f : R →+* R') : (inL R m n).map f = inL R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.one_apply]
    split_ifs <;> simp
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.zero_apply, map_zero]

theorem inR_map {R' : Type} [CommRing R'] (f : R →+* R') : (inR R m n).map f = inR R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.zero_apply, map_zero]
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.one_apply]
    split_ifs <;> simp

theorem mul_inL {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inL R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inL, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem mul_inR {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inR R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inR, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem blkMat_inL (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inL R m n = inL R m n * a := by
  rw [blkMat, inL, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

theorem blkMat_inR (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inR R m n = inR R m n * b := by
  rw [blkMat, inR, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

variable [StarRing R]

theorem inL_inL : (inL R m n)ᴴ * inL R m n = 1 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inL, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inR : (inR R m n)ᴴ * inR R m n = 1 := by
  rw [mul_inR]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inL : (inR R m n)ᴴ * inL R m n = 0 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR]

end Matrices

variable {D : D7}

def sumDec (V W : HSp D) : GlobalTheory.MixModel.OrthDec (sumSp V W) V W where
  iA := inL D.host.E V.rank W.rank
  iB := inR D.host.E V.rank W.rank
  isoA := by
    change (inL D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = V.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inL_inL, Matrix.one_mul]
  isoB := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inR D.host.E V.rank W.rank = W.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inR, ← Matrix.mul_assoc, inR_inR, Matrix.one_mul]
  orth := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = 0
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inR_inL, Matrix.zero_mul]
  rank_add := rfl

theorem sumDec_jA (V W : HSp D) : (sumDec V W).jA = inL (AE D) V.rank W.rank := inL_map (incA D)

theorem sumDec_jB (V W : HSp D) : (sumDec V W).jB = inR (AE D) V.rank W.rank := inR_map (incA D)

theorem sumDec_emb (V W : HSp D) (g : GA D V) (g' : GA D W) : (sumDec V W).emb (g, g') = ioSum V W (g, g') := by
  refine GlobalTheory.MixModel.mt_injective _ ?_
  have hA : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jA = HMul.hMul (sumDec V W).jA (mt V g) := by
    rw [sumDec_jA]; exact blkMat_inL (mt V g) (mt W g')
  have hB : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jB = HMul.hMul (sumDec V W).jB (mt W g') := by
    rw [sumDec_jB]; exact blkMat_inR (mt V g) (mt W g')
  rw [GlobalTheory.MixModel.OrthDec.mt_emb, ← hA, ← hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
    GlobalTheory.MixModel.OrthDec.sum_eq_one, Matrix.mul_one]

theorem boxS_apply (A B : HSp D) (f : WO A B → ℂ) (f' : WO (negSp A) B → ℂ) (x : WO (dblSp A) B) :
    (sumDec A (negSp A)).boxS B f f' x = f (resL A B x) * f' (resR A B x) := by
  rw [GlobalTheory.MixModel.OrthDec.boxS, GlobalTheory.MixModel.OrthDec.resS_apply, sumDec_jA, sumDec_jB]
  exact congrArg₂ (· * ·) (congrArg f (mul_inL x)) (congrArg f' (mul_inR x))

theorem thetaClause : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ThetaClause ψ A B χB om omh := by
  intro D ψ A B χA χB om omh hom homh f₁ f₂ h₁ h₂
  refine ⟨GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char D ψ A B hom.std f₁ f₂ h₁ h₂, fun g₁ g₂ h => ?_⟩
  obtain ⟨hθ, om', hom', hact⟩ := GlobalTheory.T.exists_conjugate_weilDatum_hermitianSpaceNeg D ψ A B χA χB om hom
  have hT := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hom.std (sumSp A (negSp A)) A (negSp A) (sumDec A (negSp A)) B
  have hh : IsWeilDatumO ψ (sumSp A (negSp A)) B (χA * χA⁻¹) χB omh := by rw [mul_inv_cancel]; exact homh
  have key := hT.om_box χA χA⁻¹ χB omh om om' hh hom hom' g₁ ((negEquiv A).symm g₂) h f₁ _ h₁ (hθ f₂ h₂)
  rw [hact _ h f₂ h₂, sumDec_emb, io_eq_ioSum, MulEquiv.apply_symm_apply] at key
  have e : (sumDec A (negSp A)).boxS B f₁ (fun x => conj (f₂ (-x))) = delta A B f₁ f₂ :=
    funext fun x => boxS_apply A B _ _ x
  have main : omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
      (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) := by
    rw [← e]
    refine key.trans (funext fun x => (boxS_apply A B _ _ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨main, ?_⟩
  have zL : resL A B 0 = 0 := rfl
  have zR : resR A B 0 = 0 := rfl
  rw [thetaKO, main]
  simp only [thetaKO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul, zL, zR, neg_zero]
  ring

end GlobalTheory.DoublingTheta

end
