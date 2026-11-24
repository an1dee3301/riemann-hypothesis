module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameTransport

theorem colLat_inv_mulVec_int {K : Type} [Field K] [NumberField K] {n : ℕ} (fr : GL (Fin n) K)
    (x : Fin n → K) (hx : x ∈ colLat fr) : ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K := by
  let M : Submodule (𝓞 K) (Fin n → K) :=
    { carrier := {x | ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : fr⁻¹.val *ᵥ (c • a) = (algebraMap (𝓞 K) K c) • (fr⁻¹.val *ᵥ a) := by
          rw [← Matrix.mulVec_smul, algebraMap_smul]
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem ⟨c, rfl⟩ (ha i) }
  have hle : colLat fr ≤ M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ i
    have hcol : (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j) = fr.val *ᵥ Pi.single j 1 := by
      rw [Matrix.mulVec_single_one]; rfl
    show (fr⁻¹.val *ᵥ (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j)) i ∈ _
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : i = j
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  exact hle hx

theorem inclEAf_intOE_mem {D : D7} (e : D.host.E) (he : e ∈ Formalism.UG.intOE D.host.E) :
    inclEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)


set_option maxHeartbeats 1000000 in
theorem hatL_colLat_coord_int {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    ∀ i, ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  let S := Formalism.L2.Herm.intAf D.host.F D.host.E
  let P : Matrix (Fin n) (Fin n) (Lev.EAf D) := (Formalism.UG.bc (inclEAf D) fr)⁻¹.val
  have hP : P = (fr⁻¹.val).map (inclEAf D) := rfl
  let M : Submodule S (Fin n → Lev.EAf D) :=
    { carrier := {y | ∀ i, (P *ᵥ y) i ∈ S}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : P *ᵥ (c • a) = (c : Lev.EAf D) • (P *ᵥ a) := by
          rw [← Matrix.mulVec_smul]; rfl
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem c.2 (ha i) }
  have hle : Submodule.span S ((fun x : Fin n → D.host.E => fun i =>
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) '' (colLat fr : Set (Fin n → D.host.E))) ≤ M := by
    refine (Submodule.span_le (p := M)).2 ?_
    rintro _ ⟨x, hx, rfl⟩ i
    have h1 := colLat_inv_mulVec_int fr x hx i
    have h2 : (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i =
        inclEAf D ((fr⁻¹.val *ᵥ x) i) := by
      rw [hP, RingHom.map_mulVec]; rfl
    show (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i ∈ S
    rw [h2]
    exact inclEAf_intOE_mem _ h1
  exact hle hy

end GlobalTheory.FrameTransport

end
