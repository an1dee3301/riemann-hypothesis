module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
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
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_span_fin_of_fg {L : Type} [Field L] (O : ValuationSubring L) (n : ℕ) (N : Submodule O (Fin n → L))
    (hN : N.FG) : ∃ c : Fin n → Fin n → L, N = Submodule.span O (Set.range c) := by
  classical
  have : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  have : Module.Flat O N :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let k := Module.finrank O N
  let B : Module.Basis (Fin k) O N := Module.finBasis O N
  have hli : LinearIndependent O (fun i => (B i : Fin n → L)) :=
    B.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hliL : LinearIndependent L (fun i => (B i : Fin n → L)) :=
    (LinearIndependent.iff_fractionRing O L).1 hli
  have hk : k ≤ n := by simpa using hliL.fintype_card_le_finrank
  refine ⟨fun j => if h : (j : ℕ) < k then (B ⟨j, h⟩ : Fin n → L) else 0, le_antisymm ?_ ?_⟩
  · have hsp : N = Submodule.span O (Set.range fun i => (B i : Fin n → L)) := by
      have h1 := congrArg (Submodule.map N.subtype) B.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
      exact h1.symm
    refine hsp.le.trans (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by simp⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : (j : ℕ) < k
    · simp [h]
    · simp [h]

theorem mem_span_cols_iff {L : Type} [Field L] (O : ValuationSubring L) {n : ℕ} {ι : Type} [Fintype ι]
    (M : Matrix (Fin n) ι L) (v : Fin n → L) :
    v ∈ Submodule.span O (Set.range fun j i => M i j) ↔ ∃ u : ι → L, (∀ i, u i ∈ O) ∧ v = M *ᵥ u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => c j, fun j => (c j).2, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun j => ⟨u j, hu j⟩, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_square_span_cols : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) ι L), ∃ b : Matrix (Fin n) (Fin n) L, ∀ v : Fin n → L,
      (∃ u : ι → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = M *ᵥ u) ↔ ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
  intro L _ _ n ι _ _ M
  let O : ValuationSubring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  obtain ⟨c, hc⟩ := exists_span_fin_of_fg O n (Submodule.span O (Set.range fun j i => M i j))
    (Submodule.fg_span (Set.finite_range _))
  refine ⟨Matrix.of fun i j => c j i, fun v => ?_⟩
  have h1 := mem_span_cols_iff O M v
  have h2 := mem_span_cols_iff O (Matrix.of fun i j => c j i) v
  rw [hc] at h1
  exact h1.symm.trans h2

end GlobalTheory.Hk3.HoweG
