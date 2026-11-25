module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PlaceInt.LocBasis
open NumberField Module
open scoped nonZeroDivisors

theorem exists_basis_up_to {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A] [Algebra A E]
    [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : ℕ} (L : Submodule O (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ (s : S) (b : Fin n → Fin n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hM
  have : Submodule.IsFullLattice E M :=
    { toIsLattice := Submodule.IsLattice.of_fg E <| by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  haveI : Module.Finite A M := Submodule.IsLattice.finite E M
  let c : Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : Fin n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (Fin n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : Fin n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis (Fin n) A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : Fin n → E) = (t i : O) • (c i : Fin n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : Fin n → Fin n → E := fun i => (c' i : Fin n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsFullLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsFullLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy




end GlobalTheory.PlaceInt.LocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.LocBasis

end GlobalTheory.PlaceInt.LocBasis
