module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPowStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionInverseTransposeMaximalMinorProductStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem om_real_fock_eq : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
  ∀ g ∈ GinfC X.A, ∀ T, X.om (g, 1) (X.fock T) = X.fock T := by
  intro D cc δ t0 Q P X hX hB g hg T
  set G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.A g) with hG
  have hmt : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B (1 : GA D X.B)) = 1 := fun τ => by
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one]
  have hmove := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * G τ) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 * 1) g 1
    (fun τ => by simp) (fun τ => by simp) (fun τ => by simp [hG]) (fun τ => by rw [hmt])
    X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))).2
  have hsub := GlobalTheory.FockBaseChange.pureTensorO_subst D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) G
    (fun _ => 1) (fun _ => 1) X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  have hdet : ∀ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * ((G τ)⁻¹).det = 1 := fun τ => by
    have e := GlobalTheory.WeilVacMove.compAt_mt_mul_inv X.θ τ X.A g
    have hu : IsUnit (G τ) := IsUnit.of_mul_eq_one _ e
    rw [← Matrix.det_mul]
    rw [show compAt X.θ τ (Formalism.L2.Theta.mt X.A g) = G τ from rfl,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.det_one]
  change X.om (g, 1) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))) = pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))
  rw [hmove, GlobalTheory.T.norm_pair_real_points_smul_adelic_vacuum_det_pow P X hX hB g hg, GlobalTheory.FiniteFock.pureTensorO_smul, hsub, GlobalTheory.T.substitution_inverse_transpose_maximalMinorProduct P X T G, map_smul, smul_smul,
    ← Finset.prod_mul_distrib]
  simp only [← mul_pow, hdet, one_pow, Finset.prod_const_one, one_smul]

end GlobalTheory.NormDict
