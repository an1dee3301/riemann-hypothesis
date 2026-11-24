module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Formalism.SatakeDualWeyl.StatementE
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem latAt_sumLat_self {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) :
    latAt w (sumLat finSumFinEquiv L L) = sumLat finSumFinEquiv (latAt w L) (latAt w L) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have hl0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0 := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hr0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hls : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e (c • x) 0 = c • pairVec e x 0 := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hrs : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e 0 (c • x) = c • pairVec e 0 x := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hz : pairVec e (0 : Fin n → w.adicCompletion E) 0 = 0 := by
    funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y := by
    intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_sumLat] at hx ⊢
    exact ⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩
  · intro z hz'
    rw [← pairVec_eta e z, pairVec_mem_sumLat] at hz'
    rw [← pairVec_eta e z, hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inl i)) := ⟨_, rfl⟩
      have hu' := hz'.1
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨hy, L.zero_mem⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hl0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hls]; exact Submodule.smul_mem _ c hx
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inr i)) := ⟨_, rfl⟩
      have hu' := hz'.2
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨L.zero_mem, hy⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hr0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hrs]; exact Submodule.smul_mem _ c hx

theorem isFrameAt_sumLat_blkGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro E _ _ w n L a ha y
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  rw [latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat,
    ← ha, ← ha]
  constructor
  · intro h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩
  · rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]

end GlobalTheory.LFun
