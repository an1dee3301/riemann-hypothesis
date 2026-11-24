module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Group

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StabMove

theorem mul_entries_mem {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) (hN : ∀ i j, N i j ∈ R) :
    ∀ i j, (M * N) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem R fun k _ => R.mul_mem (hM i k) (hN k j)

def lift {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ⟨M i j, hM i j⟩

theorem lift_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) :
    (lift R M hM).map R.subtype = M := by
  ext i j; rfl

def liftGL {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) : GL (Fin n) R where
  val := lift R u.val hu
  inv := lift R (u⁻¹).val hu'
  val_inv := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.inv_mul

theorem liftGL_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) :
    Formalism.UG.bc R.subtype (liftGL R u hu hu') = u := by
  ext i j; rfl

end GlobalTheory.StabMove

open GlobalTheory.StabMove in
theorem GlobalTheory.StabMove.finE_mem_St : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  intro D V g β₀ β₁ h₀ h₁ ε φ hε hφ hg hg'
  set R := Formalism.L2.Herm.intAf D.host.F D.host.E with hR
  have hcF : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D), (∀ i j, M i j ∈ R) →
      ∀ i j, ((M.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro M hM i j
    exact GlobalTheory.LevSplit.sigR_int (hM j i)
  have hshape : ∀ (a b : GL (Fin V.rank) (Lev.EAf D)), (∀ i j, a.val i j ∈ R ∧ (a⁻¹).val i j ∈ R) →
      (∀ i j, b.val i j ∈ R ∧ (b⁻¹).val i j ∈ R) →
      ∀ i j, ((1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
        ε • (a * b⁻¹).val + φ • ((b * a⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro a b ha hb i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine R.add_mem (R.add_mem (R.mul_mem ?_ ?_) (R.mul_mem hε ?_)) (R.mul_mem hφ ?_)
    · exact R.sub_mem (R.sub_mem R.one_mem hε) hφ
    · rw [Matrix.one_apply]; split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).2) i j
    · apply hcF
      rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (hb i j).1) (fun i j => (ha i j).2)
  have hE : ∀ i j, (Formalism.IndefR.Lev.finE V g).val i j ∈ R := by
    have : (Formalism.IndefR.Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl
    rw [this, hg]; exact hshape β₁ β₀ h₁ h₀
  have hE' : ∀ i j, ((Formalism.IndefR.Lev.finE V g)⁻¹).val i j ∈ R := by
    have : ((Formalism.IndefR.Lev.finE V g)⁻¹).val = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
      rw [← map_inv]; rfl
    rw [this, hg']; exact hshape β₀ β₁ h₀ h₁
  set u := β₁⁻¹ * Formalism.IndefR.Lev.finE V g * β₁ with hu
  have hu1 : ∀ i j, u.val i j ∈ R := by
    intro i j
    simp only [hu, Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE) (fun i j => (h₁ i j).1) i j
  have hu2 : ∀ i j, (u⁻¹).val i j ∈ R := by
    intro i j
    have : u⁻¹ = β₁⁻¹ * (Formalism.IndefR.Lev.finE V g)⁻¹ * β₁ := by
      simp only [hu, mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    simp only [Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE') (fun i j => (h₁ i j).1) i j
  refine ⟨liftGL R u hu1 hu2, ?_⟩
  show MulAut.conj β₁ (Formalism.UG.bc R.subtype (liftGL R u hu1 hu2)) = _
  rw [liftGL_map, MulAut.conj_apply, hu]
  group
