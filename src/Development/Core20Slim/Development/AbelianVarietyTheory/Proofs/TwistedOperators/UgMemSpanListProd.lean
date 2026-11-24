module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymbolCongr
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Function
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Congruence.Basic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem ug_mem_span_listProd (p q : ℕ) (u : Ug p q) :
    u ∈ Submodule.span ℂ {u : Ug p q | ∃ l : List (Mat p q), u = (l.map (ugι p q)).prod} := by
  have htop : Algebra.adjoin ℂ (Set.range (ugι p q)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (Mat p q)) :=
      RingCon.mkₐ_surjective _
    obtain ⟨t, rfl⟩ := hs x
    induction t using TensorAlgebra.induction with
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | ι y => exact Algebra.subset_adjoin ⟨y, rfl⟩
    | mul a b ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
    | add a b ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
  have hu : u ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (ugι p q))) := by
    rw [Subalgebra.mem_toSubmodule, htop]
    exact Algebra.mem_top
  rw [Algebra.adjoin_eq_span] at hu
  refine Submodule.span_mono (fun x hx => ?_) hu
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    exact ⟨[m], by simp⟩
  | one => exact ⟨[], by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨la, rfl⟩ := ha
    obtain ⟨lb, rfl⟩ := hb
    exact ⟨la ++ lb, by simp [List.map_append, List.prod_append]⟩

theorem iSup_indF_eq_top (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : (⨆ k, indF act k) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective (indRel act) z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb
  | tmul u v =>
    have hu := ug_mem_span_listProd p q u
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨l, rfl⟩ := hw
      refine Submodule.mem_iSup_of_mem l.length (Submodule.subset_span ⟨_, ?_, v, rfl⟩)
      exact Submodule.subset_span ⟨l, le_rfl, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [TensorProduct.add_tmul, map_add (f := _)]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Submodule.smul_mem _ c ha

end GlobalTheory.InducedPBW
