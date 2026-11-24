module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SbHalfHalfInd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemLoc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
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
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

set_option maxHeartbeats 800000 in
theorem splitOrInert (D : D7) : LevelGroupLemmas.SplitOrInert D := by
  intro v ε hε
  by_cases h : ∃ e : AE D, IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0
  · left
    obtain ⟨e, ⟨h1, h2, w, ε', hpl, hs⟩, hne⟩ := h
    rw [placeIdem_eq hpl] at hs
    change e + cA D e = phiE w 1 at hs
    rw [placeIdem_eq hε] at hne
    change e * phiE v 1 ≠ 0 at hne
    have heps : e * phiE w 1 = e := by rw [← hs, mul_add, h1, h2, add_zero]
    have hwv : w = v := by
      by_contra hwv
      apply hne
      rw [← heps, mul_assoc, phiE_orth hwv, mul_zero]
    subst hwv
    obtain ⟨s, ι, hss, hι⟩ := split_emb h1 h2 hs
    refine ⟨plOf ι, ?_, plOf_split ι s hss hι⟩
    have hle : w.asIdeal ≤ (belowPl (plOf ι)).asIdeal := fun f hf => algebraMap_mem_valIdeal ι hf
    exact (w.isMaximal.eq_of_le (belowPl (plOf ι)).isPrime.ne_top hle).symm
  · right
    intro e he
    by_contra hne
    exact h ⟨e, he, hne⟩

end Formalism.IndefR.Fin

end
