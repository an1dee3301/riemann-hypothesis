module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.BotFormula

theorem toFinE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = GlobalTheory.CuspRep.conjFin (D.host.conj : D.host.E ≃+* D.host.E) (toFinE D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul x a =>
    change GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] D.host.conj x) =
      GlobalTheory.CuspRep.conjFin _ (GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] x))
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul,
      GlobalTheory.DefU.ClassFin.conjFin_adMap _ (fun q => D.host.conj.commutes q), GlobalTheory.CuspRep.conjFin_algebraMap]
    rfl

def toAfE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* TensorProduct D.host.F (Af D.host.F) D.host.E :=
  (toFinE D).trans (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm

theorem toAfE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toAfE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = sigR (Af D.host.F) D.sp.cm.sig (toAfE D y) := by
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun x => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D x)]
  simp only [toAfE, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact toFinE_sgA D y

theorem exists_isFinPt_of_gram_one : ∀ {D : D7} (WW : HSp D), WW.gram = 1 → ∀ {n : ℕ} (h : GA D n), WW.rank = n →
    ∃ g : GA D WW, GlobalTheory.BotFormula.IsFinPt WW g h := by
  intro D WW hG n h hr
  subst hr
  let x' : GL (Fin WW.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := Formalism.UG.bc (toAfE D).toRingHom h.1
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * h.1 = 1 := by
    have h2 := h.2
    change Formalism.UG.cT _ (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hx' : x' ∈ HR (Af D.host.F) D.sp.cm.sig WW.gram := by
    show Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) *
      JR (Af D.host.F) WW.gram * (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) = JR (Af D.host.F) WW.gram
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact GlobalTheory.DefU.ClassFin.unitary_map (toAfE D).toRingHom (Formalism.MainNotions.StandardLatticesGL3.sgA D) _ (toAfE_sgA D) _ hh
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue WW 1 x' (one_mem _) hx'
  refine ⟨k, k1, rfl, fun i j => ?_⟩
  rw [k2]
  exact (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _

end GlobalTheory.BotFormula
