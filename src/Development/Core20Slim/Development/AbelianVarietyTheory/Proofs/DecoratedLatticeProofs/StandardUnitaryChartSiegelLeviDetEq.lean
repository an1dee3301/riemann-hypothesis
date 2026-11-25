module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
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
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
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

open Matrix GlobalTheory.Doubling

theorem chart_lowerLeft_zero {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) (i j : Fin n) :
    mat g (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  have hx : (Pi.single (Fin.castAdd n j) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
    rw [upperHalf, LinearMap.mem_ker]
    funext k
    rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega) _
  have h1 := (hg (Pi.single (Fin.castAdd n j) 1)).1 hx
  rw [upperHalf, LinearMap.mem_ker] at h1
  have h2 := congrFun h1 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right, mulVec_single_one] at h2
  exact h2

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_levi_mul {D : D7} {A : HSp D} {μ : D.host.E} {κ : GA D (dblSp A) ≃* G D A.rank}
    (hκ : IsChart A μ κ) (p : GA D (dblSp A)) (hp : κ p ∈ P D A.rank) :
    leviMat finSumFinEquiv (mt (dblSp A) p) * rat A.gram⁻¹ = rat A.gram⁻¹ * blkA (mat (κ p)) := by
  ext i j
  have h := congrFun (congrFun (hκ p) (Fin.castAdd A.rank i)) (Fin.castAdd A.rank j)
  simp only [Matrix.mul_apply, Fin.sum_univ_add] at h
  simp only [Matrix.mul_apply, leviMat, blkA, toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, submatrix_apply, add_mul,
    Finset.sum_add_distrib, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp only [Tm, rat, Matrix.map_apply, submatrix_apply, id, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr, dblDec, stackRows,
    fromRows_apply_inl, fromRows_apply_inr, chart_lowerLeft_zero hp, mul_zero, Finset.sum_const_zero, add_zero] at h
  simp only [Matrix.add_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib, rat, Matrix.map_apply]
  exact h.symm

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_aP_eq_det : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (p : siegel A) (a : GL (Fin A.rank) (AE D)), blkA (mat (κ p)) = a.1 →
      aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A μ hμ κ hκ p a ha
  have hP : κ p ∈ P D A.rank := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ p).1 p.2
  have h1 := congrArg Matrix.det (chart_levi_mul hκ p hP)
  rw [ha, Matrix.det_mul, Matrix.det_mul] at h1
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (gram_det_ne A)
  refine Units.ext ?_
  change (leviMat finSumFinEquiv (mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  exact hu.mul_left_cancel (by rw [mul_comm]; exact h1)

end GlobalTheory.StdUnn

end
