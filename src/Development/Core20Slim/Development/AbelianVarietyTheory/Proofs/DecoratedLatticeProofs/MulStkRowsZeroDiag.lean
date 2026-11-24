module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverseStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KeepsDiagOfMulStkRowsOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix

variable {D : D7}

theorem Tm_mul_stackRows_gram (A : HSp D) (μ : D.host.E) :
    Tm A μ * stackRows A.gram 0 = stackRows 1 1 := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  rw [Tm, stackRows, submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (stackRows A.gram⁻¹ A.gram⁻¹ * A.gram).submatrix id id = stackRows 1 1
  rw [submatrix_id_id]
  show stkRows A.gram⁻¹ A.gram⁻¹ * A.gram = stkRows 1 1
  rw [stkRows_mul, nonsing_inv_mul _ hG]

theorem mul_stkRows_zero_diag {n : ℕ} (F : Mx D (n + n) (n + n))
    (hF : ∀ i j : Fin n, F (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) =
      F (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)))
    (X : Mx D n n) :
    ∃ β : Mx D n n, F ⬝ (stkRows X 0 : Mx D (n + n) n) = stkRows β β := by
  refine ⟨(F ⬝ (stkRows X 0 : Mx D (n + n) n)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id, ?_⟩
  ext a j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective a
  simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]
  rcases s with s | s
  · simp only [Matrix.fromRows_apply_inl, Matrix.submatrix_apply, id]
  · simp only [Matrix.fromRows_apply_inr, Matrix.submatrix_apply, id, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp]
    simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hF]

theorem exists_siegel_mul_Tm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ Fr : GL (Fin (A.rank + A.rank)) (AE D), adj Fr.1 * gA (dblSp A) * Fr.1 = incA D μ • rat (Jst D A.rank) → (∀ i j : Fin A.rank, Fr.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) = Fr.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) → ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1 := by
  intro D A μ hμ Fr hFr hdiag
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTT : Tm A μ * (Tm A μ)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hTT' : (Tm A μ)⁻¹ * Tm A μ = 1 := nonsing_inv_mul _ hdet
  have hU : adj (Fr.1 * rat (Tm A μ)⁻¹) * (gA (dblSp A) * (Fr.1 * rat (Tm A μ)⁻¹)) = gA (dblSp A) := by
    have h1 : rat ((Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹) = rat (dblSp A).gram := by
      congr 1
      rw [show (Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹ =
          (Tm A μ * (Tm A μ)⁻¹)ᴴ * (dblSp A).gram * (Tm A μ * (Tm A μ)⁻¹) by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc], hTT, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hgram, rat_mul, rat_mul, rat_smul, ← hFr, rat_conjTranspose,
      show rat (dblSp A).gram = gA (dblSp A) from rfl] at h1
    rw [adj_mul]
    simp only [Matrix.mul_assoc] at h1 ⊢
    exact h1
  have hS : (Fr.1 * rat (Tm A μ)⁻¹ : Mx D (A.rank + A.rank) (A.rank + A.rank)) ⬝
      (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = Fr.1 ⬝ (stkRows (gA A) 0 : Mx D (A.rank + A.rank) A.rank) := by
    rw [show (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = rat (stackRows 1 1) by rw [rat_stackRows, rat_one],
      ← Tm_mul_stackRows_gram A μ, rat_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (rat (Tm A μ)⁻¹), ← rat_mul, hTT',
      rat_one, Matrix.one_mul, rat_stackRows, rat_zero]
    rfl
  obtain ⟨β, hβ⟩ := mul_stkRows_zero_diag Fr.1 hdiag (gA A)
  refine ⟨⟨ofMat (dblSp A) _ hU, mem_siegelOf.2 (keepsDiag_of_mul_stkRows_one (β := β) (hS.trans hβ))⟩, ?_⟩
  show (Fr.1 * rat (Tm A μ)⁻¹) * rat (Tm A μ) = Fr.1
  rw [Matrix.mul_assoc, ← rat_mul, hTT', rat_one, Matrix.mul_one]

end GlobalTheory.StdUnn
