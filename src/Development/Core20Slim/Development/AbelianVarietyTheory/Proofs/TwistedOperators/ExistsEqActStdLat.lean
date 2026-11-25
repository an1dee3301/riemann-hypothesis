module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentTerms
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_eq_act_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsFullLattice k L) :
    ∃ g : GL ι k, L = act g (stdLat k ι) := by
  haveI := hL
  haveI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  haveI : Module.Finite 𝒪[k] L := Module.Finite.iff_fg.mpr hL.fg
  have hr : Module.finrank 𝒪[k] L = Fintype.card ι := ((Submodule.IsFullLattice.finrank_eq k L).trans (Module.finrank_fintype_fun_eq_card k))
  let b : Module.Basis ι 𝒪[k] L :=
    (Module.finBasisOfFinrankEq 𝒪[k] L hr).reindex (Fintype.equivFin ι).symm
  let c : Module.Basis ι k (ι → k) := b.extendOfIsLattice k
  have hc : ∀ i, c i = (b i : ι → k) := fun i => Module.Basis.extendOfIsLattice_apply k b i
  let A : Matrix ι ι k := Matrix.of fun i j => (b j : ι → k) i
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : A.col = c := by
      funext j i
      rw [hc]; rfl
    rw [this]; exact c.linearIndependent
  obtain ⟨g, hg⟩ := hA
  have key : ∀ a : ι → 𝒪[k], (g : Matrix ι ι k) *ᵥ (fun i => (a i : k))
      = ((∑ j, a j • b j : L) : ι → k) := by
    intro a
    funext i
    rw [hg, Submodule.coe_sum, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Submodule.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  refine ⟨g, ?_⟩
  ext v
  rw [mem_act]
  constructor
  · intro hv
    refine ⟨fun i => (b.repr ⟨v, hv⟩ i : k), mem_stdLat.2 fun i => (b.repr ⟨v, hv⟩ i).2, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨w, hw, rfl⟩
    rw [mem_stdLat] at hw
    have := key fun i => ⟨w i, hw i⟩
    change (g : Matrix ι ι k) *ᵥ w = _ at this
    rw [this]
    exact Subtype.property _

end GlobalTheory.RootEx.UnfoldShape
