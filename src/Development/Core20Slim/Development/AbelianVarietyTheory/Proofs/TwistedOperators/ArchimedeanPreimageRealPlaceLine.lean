module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransportStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ArchLinePreimage

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem smul_eq_zero_of_finPart_eq_zero (t : AE D) (ht : finPart D t = 0) (a : AF D.host.F)
    (ha : a.1 = 0) : a • t = 0 := by
  let ι : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F →ₗ[D.host.F] AF D.host.F :=
    (LinearMap.inr D.host.F (InfiniteAdeleRing D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)).comp
      (LinearMap.mulLeft D.host.F a.2)
  let g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
    TensorProduct.map ι LinearMap.id
  let fL : AE D →ₗ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    TensorProduct.map (sndA D.host.F).toLinearMap LinearMap.id
  have hfL : fL t = finPart D t := rfl
  have key : ∀ s : AF D.host.F ⊗[D.host.F] D.host.E, a • s = g (fL s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [smul_zero, LinearMap.map_zero, LinearMap.map_zero]
    | tmul b x =>
      have hab : a * b = ι b.2 := by
        refine Prod.ext ?_ ?_
        · show a.1 * b.1 = 0
          rw [ha, zero_mul]
        · rfl
      have h1 : a • (b ⊗ₜ[D.host.F] x : AE D) = (a * b) ⊗ₜ[D.host.F] x := rfl
      rw [h1, hab]
      rfl
    | add s₁ s₂ h₁ h₂ =>
      rw [smul_add, h₁, h₂, LinearMap.map_add (f := _), LinearMap.map_add (f := _)]
  rw [key, hfL, ht, LinearMap.map_zero]

theorem arch_symm_lineAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS.symm (lineAt θ τ z 1)) := by
  intro D θ hθ ε S X d e cS hcS τ z u hu
  have hx : (lineAt θ τ z 1).map (finPart D) = 0 :=
    funext fun i => funext fun j => congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z).2.1 1) i) j
  set y := cS.symm (lineAt θ τ z 1) with hydef
  have hy := cS.apply_symm_apply (lineAt θ τ z 1)
  rw [← hydef, hcS] at hy
  set c : D.host.E := if ε then -1 else 1 with hc
  have hc0 : c ≠ 0 := by rw [hc]; split_ifs <;> norm_num
  set N : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (c • S.gram).map ((finPart D).comp (inclR (AF D.host.F))) with hN
  have hNdet : IsUnit N.det := by
    have hd : N.det = ((finPart D).comp (inclR (AF D.host.F))) (c • S.gram).det :=
      (RingHom.map_det ((finPart D).comp (inclR (AF D.host.F))) _).symm
    rw [hd]
    refine IsUnit.map _ (Ne.isUnit ?_)
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc0) (gram_det_ne S)
  have hM : (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
      Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = 0 := by
    have h3 := congrArg (fun m => Matrix.map m (finPart D)) hy
    simp only [Matrix.map_mul] at h3
    rw [hx] at h3
    exact h3
  have hM0 : (y.map (finPart D))ᵀ.submatrix e id = 0 := by
    calc _ = HMul.hMul (HMul.hMul ((y.map (finPart D))ᵀ.submatrix e id) N :
          Matrix (Fin X.rank) (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) N⁻¹ :=
          (Matrix.mul_nonsing_inv_cancel_right N _ hNdet).symm
      _ = 0 := by rw [hM, Matrix.zero_mul]
  have hent : ∀ i j, finPart D (y i j) = 0 := by
    intro i j
    have h4 := congrFun (congrFun hM0 (e.symm j)) i
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply, Equiv.apply_symm_apply,
      id, Matrix.zero_apply] at h4
    exact h4
  have hu1 : u.1 = 0 := by
    have h5 : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 h5
  funext i j
  exact smul_eq_zero_of_finPart_eq_zero (y i j) (hent i j) u hu1

end GlobalTheory.ArchLinePreimage
