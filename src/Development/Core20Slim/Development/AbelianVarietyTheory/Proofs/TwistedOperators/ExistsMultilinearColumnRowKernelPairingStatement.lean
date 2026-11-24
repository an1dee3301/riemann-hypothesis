module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_columnRowKernelPairing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∃ M : MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => thSub W (.top t j))
        (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  intro D T L sc G W U S t x y Ψ₀ F₀
  have chain {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] :
      ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
        (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
        ∃ M : MultilinearMap (RingHom.id ℂ) A (V 0 →ₗ[ℂ] V m), ∀ fs,
          M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
    intro m
    induction m with
    | zero =>
      intro A _ _ k
      exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) A LinearMap.id, fun _ => rfl⟩
    | succ m ih =>
      intro A _ _ k
      obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
      let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
      refine ⟨MultilinearMap.uncurryRight
        (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M),
        fun fs => ?_⟩
      show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
      rw [hM]
      beta_reduce
      rw [dite_eq_left (Nat.lt_succ_self m)]
      congr 1
      refine GlobalTheory.ArrowMultilinear.chainTo_congr m fun j hj => ?_
      rw [dite_eq_left hj, dite_eq_left (Nat.lt_succ_of_lt hj)]
      rfl
  obtain ⟨Mc, hc⟩ := chain (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.top t j)
        (x j * S.N.u _) (x (j + 1) * S.N.u _))
  obtain ⟨Mr, hr⟩ := chain (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.chi i D.R.m : Pair T)
        (y i * S.N.u _) (y (i + 1) * S.N.u _))
  let col := (LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc
  let row := (LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr
  have hcol (fs : ∀ j : Fin D.R.m, thSub W (.top t j)) :
      col fs = colMapV S (t := t) (fun j => (fs j : WO _ _ → ℂ)) x Ψ₀ := by
    show Mc fs _ = _
    rw [hc]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  have hrow (gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) :
      row gs = rowMapV S (fun i => (gs i : WO _ _ → ℂ)) y F₀ := by
    show Mr gs _ = _
    rw [hr]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  let β := brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))
  let pairWithRow : VV ℂ (wt G (.top D.R.m)) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ :=
    { toFun := fun v => (β v).compMultilinearMap row
      map_add' := fun v v' => by
        ext gs
        change β (v + v') (row gs) = β v (row gs) + β v' (row gs)
        simp only [map_add]
        rfl
      map_smul' := fun c v => by
        ext gs
        change β (c • v) (row gs) = c • β v (row gs)
        simp only [map_smul]
        rfl }
  refine ⟨pairWithRow.compMultilinearMap col, fun fs gs => ?_⟩
  show β (col fs) (row gs) = _
  rw [hcol, hrow]
  rfl
