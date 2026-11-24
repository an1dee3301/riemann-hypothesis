module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapVUpdateLast
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateLast
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrowsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.FrameSignSimple
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Gcd
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Kleene
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
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

open GlobalTheory.ExpansionInvariance in
theorem pairPts_last_invariant (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U) (hβ : β ∈ S.supp t Φ) (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m)))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m))
    (hx : x D.R.m = finEmb G.sp.topDec (y D.R.m)) (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  have hm := D.R.two_le_m
  have h0x : Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0 = x 0 :=
    Function.update_of_ne (by omega) _ _
  have h0y : Function.update y D.R.m (y D.R.m * k) 0 = y 0 := Function.update_of_ne (by omega) _ _
  rw [h0x, h0y, GlobalTheory.FunObj.SumModel.finEmb_mul, ← hx]
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO W.ψ _ _ (S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO W.ψ _ _ (S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta S (defPair_top t j) (inRange_top t j) _ ((hv d hd).1 j),
      fun i => vec_theta S (defPair_chi i) (inRange_chi i) _ ((hv d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.ArrowMultilinear.pairing_multilinear S t x y (Ψ (x 0)) (F (y 0))
  set uc : PureDat G t → ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ := fun d =>
    Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D) (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D))))
    with huc
  set ur : PureDat G t → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ := fun d =>
    Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) with hur
  have thc : ∀ d ∈ τ.support, ∀ j, IsThetaFunO W.ψ _ _ (uc d j) := by
    intro d hd j
    by_cases hj : j = lastIx D
    · subst hj
      simp only [huc, Function.update_self]
      exact colShift_theta S t _ ((hth d hd).1 _)
    · simp only [huc, Function.update_of_ne hj]
      exact (hth d hd).1 j
  have thr : ∀ d ∈ τ.support, ∀ i, IsThetaFunO W.ψ _ _ (ur d i) := by
    intro d hd i
    by_cases hi : i = lastIx D
    · subst hi
      simp only [hur, Function.update_self]
      exact rowShift_theta S k ((hth d hd).2 _)
    · simp only [hur, Function.update_of_ne hi]
      exact (hth d hd).2 i
  have lhs : pairPts S τ (Function.update x D.R.m (x D.R.m * finEmb G.sp.topDec k)) (Function.update y D.R.m (y D.R.m * k))
      (Ψ (x 0)) (F (y 0)) = τ.sum fun d a => a * M (fun j => toTh W _ (uc d j)) (fun i => toTh W _ (ur d i)) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, GlobalTheory.LastColumnMove.colMapV_update_last S _ x _ ((hth d hd).1 _), GlobalTheory.LastRowMove.rowMapV_update_last S _ y _ ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (uc d j) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = uc d :=
      funext fun j => coe_toTh W _ (thc d hd j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (ur d i) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) = ur d :=
      funext fun i => coe_toTh W _ (thr d hd i)
    rw [e1, e2]
  have rhs : pairPts S τ x y (Ψ (x 0)) (F (y 0)) =
      τ.sum fun d a => a * M (fun j => toTh W _ (S.Z.vec (d.1 j))) (fun i => toTh W _ (S.Z.vec (d.2 i))) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (S.Z.vec (d.1 j)) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = fun j : Fin D.R.m => S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (S.Z.vec (d.2 i)) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh W _ ((hth d hd).2 i)
    rw [e1, e2]
  rw [lhs, rhs]
  refine GlobalTheory.funProd_multilinear_sum_eq M τ _ _ _ _ fun w v => ?_
  have key := GlobalTheory.T.productFunction_totalTensor_invariant_lastArrows S hL hde hc ht hβ hτ hv k hk w v
  simp only [Finsupp.sum] at key ⊢
  refine (Finset.sum_congr rfl fun d hd => ?_).trans (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · simp only [coe_toTh W _ (thc d hd _), coe_toTh W _ (thr d hd _)]
    rfl
  · simp only [coe_toTh W _ ((hth d hd).1 _), coe_toTh W _ ((hth d hd).2 _)]

end GlobalTheory.LastVertexInv
