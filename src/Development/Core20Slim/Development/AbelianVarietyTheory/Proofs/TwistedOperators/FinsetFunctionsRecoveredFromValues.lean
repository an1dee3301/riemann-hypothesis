module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

namespace GlobalTheory

open Module

theorem finset_functions_recovered_from_values {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ))
    (hF : ∀ u ∈ F, u ∈ V) :
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  classical
  set W : Submodule ℂ (X → ℂ) := Submodule.span ℂ (F : Set (X → ℂ)) with hWdef
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_finset ℂ F
  have hWV : W ≤ V := Submodule.span_le.mpr (fun u hu => hF u hu)
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : X → ℂ) x := fun x w => rfl
  set S : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev) with hSdef
  have hcoan : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : X → ℂ) = 0 := by
      funext x
      have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
      simpa [hev] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
    rw [← this, hcoan, Submodule.dualAnnihilator_bot]
  let b := Module.finBasis ℂ W
  have hμ : ∀ i, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord i := by
    intro i
    have : b.coord i ∈ S := by rw [hS]; trivial
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp this
  choose μ hμ using hμ
  set s : Finset X := Finset.univ.biUnion (fun i => (μ i).support) with hsdef
  have hsub : ∀ i, (μ i).support ⊆ s := fun i x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  refine ⟨s,
    fun x => ∑ i, μ i x • ((b i : W) : X → ℂ), ?_, ?_⟩
  · intro x
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hWV (b i).2))
  · intro u hu
    let w : W := ⟨u, Submodule.subset_span hu⟩
    have hw : (w : X → ℂ) = u := rfl
    have hrep : ∀ i, b.repr w i = ∑ x ∈ s, μ i x * u x := by
      intro i
      have h1 : b.repr w i = b.coord i w := rfl
      rw [h1, ← hμ i, Finsupp.sum_of_support_subset (μ i) (hsub i)]
      · simp [LinearMap.sum_apply, hev, hw]
      · intro x _; simp
    calc u = ((∑ i, b.repr w i • b i : W) : X → ℂ) := by rw [b.sum_repr w]
      _ = ∑ i, b.repr w i • ((b i : W) : X → ℂ) := by
          rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
      _ = _ := by
        simp_rw [hrep, Finset.smul_sum, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [mul_comm]

end GlobalTheory
