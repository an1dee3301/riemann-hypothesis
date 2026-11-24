module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Order.Directed
public import Mathlib.Order.Notation
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelClasses
public import Mathlib.Order.Zorn

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_maximal_stab_of_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (G : Set (Module.End ℂ V)) (R : Submodule ℂ V) (F : Finset V)
    (hF : ∀ N : Submodule ℂ V, R ≤ N → Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) :
    ∀ N : Submodule ℂ V, R ≤ N → Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  intro N hRN hN hNtop
  let s : Set (Submodule ℂ V) := {U | R ≤ U ∧ Stab G U ∧ ¬ (↑F : Set V) ⊆ ↑U}
  have hcomp := (isCompactElement_iff_le_of_directed_sSup_le _).1
    (Submodule.finset_span_isCompactElement (R := ℂ) F)
  have hNs : N ∈ s := ⟨hRN, hN, fun h => hNtop (hF N hRN hN h)⟩
  obtain ⟨M, hNM, hM⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro g hg x hx
      obtain ⟨U, hU, hxU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨U, hU, (hcs hU).2.1 g hg x hxU⟩
    · intro hFc
      have hspan : Submodule.span ℂ (↑F : Set V) ≤ sSup c := Submodule.span_le.2 hFc
      obtain ⟨U, hU, hle⟩ := hcomp c hne hdir hspan
      exact (hcs hU).2.2 (Submodule.span_le.1 hle)) N hNs
  refine ⟨M, hNM, hM.prop.2.1, fun h => hM.prop.2.2 (by rw [h]; exact fun _ _ => trivial), ?_⟩
  intro U hU hMU
  by_cases hFU : (↑F : Set V) ⊆ ↑U
  · exact Or.inr (hF U (le_trans hM.prop.1 hMU) hU hFU)
  · exact Or.inl (le_antisymm (hM.2 ⟨le_trans hM.prop.1 hMU, hU, hFU⟩ hMU) hMU)

end GlobalTheory.TensHead
