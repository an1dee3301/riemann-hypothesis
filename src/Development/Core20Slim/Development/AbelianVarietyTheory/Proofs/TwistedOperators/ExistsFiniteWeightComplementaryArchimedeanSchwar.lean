module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Compact
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Regular

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchRest

theorem exists_rest_arch : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  intro F _ _ κ _
  classical
  let I : Set (FiniteAdeleRing (𝓞 F) F) := (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)
  have hIo : IsOpen I := GroundTheory.Global.isOpen_integralFiniteAdeles
  have hIc : IsClosed I :=
    AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hIo
  have hIk : IsCompact I := GroundTheory.Global.isCompact_integralFiniteAdeles F
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => I
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hIo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => hIc
  have hSk : IsCompact S := isCompact_univ_pi fun _ => hIk
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, HasCompactSupport.intro hSk fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ S
    · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
    · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  refine ⟨fun x => g fun i => (x i).2, ?_, fun f => ⟨?_, ?_⟩⟩
  · have h0 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply]
    exact one_ne_zero
  · intro x z hz
    have hz2 : ∀ i, (z i).2 = 0 := by
      let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
      have e := hz u (by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _)
      intro i
      have e' := congrFun e i
      have h1 : (u • z) i = u * z i := rfl
      rw [h1] at e'
      have h2 : (u * z i).2 = 1 * (z i).2 := rfl
      have := congrArg Prod.snd e'
      rw [h2, one_mul] at this
      exact this
    show g (fun i => ((x + z) i).2) = g (fun i => (x i).2)
    congr 1
    funext i
    show (x i).2 + (z i).2 = (x i).2
    rw [hz2 i, add_zero]
  · have e : tens (evI F) (⇑f) (fun x => g fun i => (x i).2) = pureA F (⇑f) g := rfl
    rw [e]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩

end GlobalTheory.ArchRest
