module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.LatDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latt_eq {n d : ℕ} {t : k} (ht : t ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) k) :
    ∃ h : GL (Fin d) k, ∀ v : Fin d → k, v ∈ latt t Y₀ ↔ ∀ j, (v ᵥ* h.1) j ∈ 𝒪[k] := by
  classical
  set L := latt t Y₀ with hL
  have : Module.Finite 𝒪[k] L := by
    rw [hL, latt]
    exact Module.Finite.span_of_finite _ ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := 𝒪[k]) (M := L)
  set w : Fin m → (Fin d → k) := fun i => (b i : Fin d → k) with hw
  have hwL : ∀ i, w i ∈ L := fun i => (b i).2
  have hli : LinearIndependent k w := by
    rw [← LinearIndependent.iff_fractionRing 𝒪[k] k]
    exact b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hsum : ∀ x (hx : x ∈ L), x = ∑ i, ((b.repr ⟨x, hx⟩ i : 𝒪[k]) : k) • w i := by
    intro x hx
    have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    refine e.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact (algebraMap_smul k _ _).symm
  have hLw : ∀ x ∈ L, x ∈ Submodule.span k (Set.range w) := by
    intro x hx
    rw [hsum x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span k (Set.range w) := by
    intro x _
    have hx : x = ∑ j, (t⁻¹ * x j) • (t • Pi.single j (1 : k) : Fin d → k) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hLw _ ?_)
    exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)
  let bk := Module.Basis.mk hli hsp
  have hbk : ∀ i, bk i = w i := fun i => by simp [bk]
  have hm : m = d := by
    have := Module.finrank_eq_card_basis bk
    simpa using this.symm
  have hmem : ∀ v, v ∈ L ↔ ∀ i, bk.equivFun v i ∈ 𝒪[k] := by
    intro v
    constructor
    · intro hv i
      have : bk.equivFun v = fun i => ((b.repr ⟨v, hv⟩ i : 𝒪[k]) : k) := by
        apply bk.equivFun.symm.injective
        rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply]
        simpa only [hbk] using hsum v hv
      rw [this]
      exact (b.repr _ i).2
    · intro hc
      rw [← bk.sum_equivFun v]
      refine L.sum_mem fun i _ => ?_
      rw [hbk i, show bk.equivFun v i • w i = (⟨bk.equivFun v i, hc i⟩ : 𝒪[k]) • w i from rfl]
      exact L.smul_mem _ (hwL i)
  let bk' := bk.reindex (finCongr hm)
  let hmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.toLinearMap)ᵀ
  let Bmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.symm.toLinearMap)ᵀ
  have hB : hmat * Bmat = 1 := by
    simp only [hmat, Bmat, ← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨hmat, Bmat, hB, mul_eq_one_comm.mp hB⟩, fun v => ?_⟩
  have key : v ᵥ* hmat = bk'.equivFun v := by
    simp [hmat, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  have hre : ∀ j, bk'.equivFun v j = bk.equivFun v ((finCongr hm).symm j) := by
    intro j
    simp [bk', Module.Basis.equivFun_apply]
  show v ∈ L ↔ ∀ j, (v ᵥ* hmat) j ∈ 𝒪[k]
  rw [key, hmem]
  simp only [hre]
  exact ⟨fun H j => H _, fun H i => by simpa using H (finCongr hm i)⟩

end PositivityTheory.Sph

end
