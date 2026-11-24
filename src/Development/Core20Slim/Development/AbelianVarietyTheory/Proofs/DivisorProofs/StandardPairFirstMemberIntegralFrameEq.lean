module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
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
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdReadFrame

theorem row_mul {R : Type} [CommRing R] {P Q : R → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → Q y → P (x * y)) {b a : ℕ} {Y : Matrix (Fin b) (Fin a) R} {K : Matrix (Fin a) (Fin a) R}
    (hK : ∀ i j, Q (K i j)) {i : Fin b} (h : ∀ j, P (Y i j)) (j : Fin a) : P ((Y * K) i j) := by
  rw [Matrix.mul_apply]
  exact Finset.sum_induction _ P hadd h0 fun l _ => hmul _ _ (h l) (hK l j)

theorem row_mul_iff {R : Type} [CommRing R] {P Q : R → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → Q y → P (x * y)) {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) {β : GL (Fin a) R}
    (hK : ∀ i j, Q (β.val i j)) (hK' : ∀ i j, Q ((β⁻¹).val i j)) (i : Fin b) :
    (∀ j, P ((Y * β.val) i j)) ↔ ∀ j, P (Y i j) := by
  refine ⟨fun h j => ?_, fun h j => row_mul h0 hadd hmul hK h j⟩
  have h1 := row_mul h0 hadd hmul hK' h j
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1

theorem topL_mul {R : Type} [CommRing R] {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) (K : Matrix (Fin a) (Fin a) R) :
    topL a (Y * K) = topL a Y * K := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : i.val < b
  · simp [topL, h, Matrix.mul_apply]
  · simp [topL, h]

theorem one_inv_mul {R : Type} [CommRing R] {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) :
    ((1 : GL (Fin b) R)⁻¹).val * Y = Y := by
  rw [inv_one, Units.val_one, Matrix.one_mul]

variable {D : D7}

theorem inId_zero (I : Ideal (𝓞 D.host.E)) : InId (D := D) I 0 := ⟨zero_mem _, Ideal.zero_mem _⟩

theorem inId_add {I : Ideal (𝓞 D.host.E)} (x y : EAf D) (hx : InId I x) (hy : InId I y) : InId I (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩

theorem inId_mul {I : Ideal (𝓞 D.host.E)} (x y : EAf D) (hx : InId I x)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : InId I (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  exact ⟨mul_mem h1 hy, Ideal.mul_mem_right (⟨y, hy⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _ h2⟩

theorem frMapO_one (S T : HSp D) (β : GL (Fin S.rank) (EAf D)) (t : WO S T) :
    frMapO S T β 1 t = HMul.hMul (Matrix.of fun i j => toEAf D (t i j) : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) β.val := by
  unfold frMapO
  rw [one_inv_mul]
  rfl

theorem stdFst_frame : ∀ {D : D7} (S T : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) (β : GL (Fin S.rank) (EAf D)),
  IsIntM β.val → IsIntM (β⁻¹).val → ∀ t : WO S T, stdFst ν e 𝔪 S T β 1 t =
    if IsHalf e t ∧ (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
        ∀ i j, S.rank ≤ i.1 → InId 𝔪 (toEAf D (t i j)) then
      unitChar ν e (HMul.hMul (topL S.rank (Matrix.of fun i j => toEAf D (t i j))) β.val) else 0 := by
  intro D S T ν e 𝔪 β hβ hβ' t
  unfold stdFst
  rw [frMapO_one, topL_mul]
  refine if_congr (and_congr_right fun _ => and_congr ?_ ?_) rfl rfl
  · exact forall_congr' fun i => row_mul_iff (P := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (Q := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (zero_mem _) (fun _ _ => add_mem) (fun _ _ => mul_mem)
      (Matrix.of fun i j => toEAf D (t i j)) hβ hβ' i
  · refine forall_congr' fun i => ?_
    have h := row_mul_iff (P := InId (D := D) 𝔪) (Q := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (inId_zero 𝔪) inId_add inId_mul (Matrix.of fun i j => toEAf D (t i j)) hβ hβ' i
    exact ⟨fun H j hi => h.1 (fun l => H l hi) j, fun H j hi => h.2 (fun l => H l hi) j⟩

end GlobalTheory.StdReadFrame
