module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField

namespace GlobalTheory.VacLoc

variable {D : D7}

open scoped Classical

def indP (D : D7) (X : Set (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ X then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]⟩

theorem evalV_indP (X : Set (Pl D)) (v : Pl D) :
    evalV D.host.F v (indP D X) = if v ∈ X then 1 else 0 := rfl

theorem indicatorAdele_mem_integralAdeles (X : Set (Pl D)) : indP D X ∈ intAf D.host.F := by
  intro v; rw [evalV_indP]; by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]

theorem finiteAdele_ext {a b : Af D.host.F} (h : ∀ v, evalV D.host.F v a = evalV D.host.F v b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem indicatorAdele_singleton_mul_singleton (X Y : Set (Pl D)) : indP D X * indP D Y = indP D (X ∩ Y) := by
  apply finiteAdele_ext; intro v; rw [map_mul, evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]

theorem indicatorAdele_union_of_disjoint {X Y : Set (Pl D)} (h : Disjoint X Y) : indP D X + indP D Y = indP D (X ∪ Y) := by
  apply finiteAdele_ext; intro v; rw [map_add (f := _), evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]
  exact Set.disjoint_left.mp h hX hY

theorem indicatorAdele_univ : indP D Set.univ = 1 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_one]; simp

theorem indicatorAdele_empty : indP D ∅ = 0 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_zero]; simp

end GlobalTheory.VacLoc

end
