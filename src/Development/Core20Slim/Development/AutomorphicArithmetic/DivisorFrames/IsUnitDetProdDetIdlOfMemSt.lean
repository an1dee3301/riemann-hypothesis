module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem prod_orthogonal_idempotents {R ι : Type} [CommRing R] [DecidableEq ι] (d : R) (es : ι → R) (Z : Finset ι)
    (ho : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → es i * es j = 0) :
    ∏ w ∈ Z, (es w * d + (1 - es w)) = (∑ w ∈ Z, es w) * d + (1 - ∑ w ∈ Z, es w) := by
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : es a * ∑ w ∈ s, es w = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        ho a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) fun h => ha (h ▸ hj)
    linear_combination (d - 1) ^ 2 * h0

private theorem inv_aux {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Aˣ) (ε d d' : B)
    (hε : ε * ε = ε) (hd : d * d' = 1) (hx : f (x : A) = 1 - ε + ε * d) :
    f ((x⁻¹ : Aˣ) : A) = 1 - ε + ε * d' := by
  have h1 : f ((x⁻¹ : Aˣ) : A) * f (x : A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h2 : f (x : A) * (1 - ε + ε * d') = 1 := by
    rw [hx]; linear_combination (1 - d - d' + d * d') * hε + ε * hd
  calc f ((x⁻¹ : Aˣ) : A) = f ((x⁻¹ : Aˣ) : A) * (f (x : A) * (1 - ε + ε * d')) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

private theorem det_conj_eq {n : ℕ} {B : Type} [CommRing B] (β γ : GL (Fin n) B) :
    (β⁻¹ * γ * β : GL (Fin n) B).val.det = γ.val.det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem UpperTheory.isUnitDet_prod_detIdl_of_mem_St :
    ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)),
      IsIdemSum e Z → ∀ g : GA D S, Lev.finE S g ∈ Formalism.L2.DIV.St βS →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val
        (∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g) := by
  classical
  intro D S βS e Z hZ g hg
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hZ
  have hee : e * e = e := GlobalTheory.Tow.idemSum_mul_of_subset hZ hZ (Finset.Subset.refl Z)
  have hint := GlobalTheory.IdemRes.toEAf_mem_of_finPart
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee]))
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hZ
  have hid : ∀ w ∈ Z, GlobalTheory.RowVacScalar.idemAt w = es w := fun w hw =>
    GlobalTheory.Tow.idemAt_unique
      (Classical.epsilon_spec (p := fun a : AE D => Formalism.L2.NTheta.IsIdemAt a w) ⟨es w, hes w hw⟩) (hes w hw)
  have hval : ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = e * (Formalism.L2.Theta.mt S g).det + (1 - e) := by
    rw [Units.coe_prod, hsum, ← prod_orthogonal_idempotents _ es Z fun i hi j hj hij => GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hid w hw, GlobalTheory.RowVacScalar.detIdl_val (hes w hw).1.1]
  have hdet : toEAf D (Formalism.L2.Theta.mt S g).det = (Lev.finE S g).val.det := by
    rw [RingHom.map_det]; rfl
  have h2 : toEAf D ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = 1 - toEAf D e + toEAf D e * (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det := by
    rw [hval, det_conj_eq, map_add (f := _), map_mul, map_sub, map_one, hdet, add_comm]
  refine ⟨?_, h2, ?_⟩
  · rw [hval, map_add (f := _), map_mul, map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · obtain ⟨z, hz⟩ := hg
    have hz' : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)) = Formalism.L2.DIV.intGL _ _ _ z := by
      rw [← hz]
      show βS⁻¹ * (βS * Formalism.L2.DIV.intGL _ _ _ z * βS⁻¹) * βS = _
      group
    have hzd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det
        = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype z.val.det := by
      rw [hz', RingHom.map_det]; rfl
    have hd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det *
        (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (z⁻¹).val.det = 1 := by
      rw [hzd, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
    rw [inv_aux (toEAf D) _ _ _ _ (by rw [← map_mul, hee]) hd h2]
    exact add_mem (sub_mem (one_mem _) hint) (mul_mem hint (z⁻¹).val.det.2)
