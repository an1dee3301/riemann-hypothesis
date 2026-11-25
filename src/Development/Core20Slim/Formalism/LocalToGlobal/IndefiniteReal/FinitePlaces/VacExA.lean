module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 400000

namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDyIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop :=
  IsSplitIdem D e ∧ finPart D e ∈ intAE D ∧
    ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε


theorem fstA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : fstA D.host.F (pairA D.host.F x y) = x := rfl
theorem sndA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : sndA D.host.F (pairA D.host.F x y) = y := rfl



section Sym

variable (S T : HSp D)

end Sym

section Phi

variable (S T : HSp D)

def U0 (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', fun i j => ?_⟩
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add (f := _), ha, hb, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, fun i j => by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, fun i j => ?_⟩
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, ha, neg_zero]

theorem mem_U0 {Λ : AddSubgroup (WO S T)} {w : WO S T} :
    w ∈ U0 S T Λ ↔ ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0 := Iff.rfl

theorem le_open_neighbourhood {Λ : AddSubgroup (WO S T)} : Λ ≤ U0 S T Λ := fun u hu => ⟨u, hu, fun i j => by simp⟩

theorem open_neighbourhood_set_eq (Λ : AddSubgroup (WO S T)) :
    (U0 S T Λ : Set (WO S T)) = {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0} := by
  ext w
  simp only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]
  refine exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩
  · ext i j; exact h i j
  · have := congrFun (congrFun h i) j; simpa using this


end Phi

section Lat

variable (S T : HSp D)

variable {S T}

end Lat

end Formalism.IndefR.Fin.VacEx
