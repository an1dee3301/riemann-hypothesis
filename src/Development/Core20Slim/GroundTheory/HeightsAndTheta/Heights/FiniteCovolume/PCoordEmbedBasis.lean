module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordEmbedBasis
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module NumberField.InfinitePlace NumberField.mixedEmbedding

noncomputable section

variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]

def mixedSpaceEquivPiOfTotallyComplex [_root_.NumberField.IsTotallyComplex E] :
    mixedSpace E ≃ₗ[ℝ] (InfinitePlace E → ℂ) where
  toFun p w := p.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun g := (0, fun w => g w.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ rfl
    funext w
    exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
  right_inv _ := rfl

def embeddingBasisOfTotallyComplex [_root_.NumberField.IsTotallyComplex E] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ) :=
  (latticeBasis E).map (mixedSpaceEquivPiOfTotallyComplex E)

theorem embeddingBasisOfTotallyComplex_apply [_root_.NumberField.IsTotallyComplex E]
    (j : Free.ChooseBasisIndex ℤ (𝓞 E)) (w : InfinitePlace E) :
    embeddingBasisOfTotallyComplex E j w = w.embedding (integralBasis E j) := by
  rw [embeddingBasisOfTotallyComplex, Basis.map_apply, latticeBasis_apply]
  exact mixedEmbedding_apply_isComplex _ _ ⟨w, IsTotallyComplex.isComplex w⟩

def piSwapEquiv : (ι → InfinitePlace E → ℂ) ≃ₗ[ℝ] (InfinitePlace E → ι → ℂ) :=
  { Equiv.piComm (fun (_ : ι) (_ : InfinitePlace E) => ℂ) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem CoordEmbedBasis.proof [_root_.NumberField.IsTotallyComplex E] : CoordEmbedBasis.Statement E ι := by
  classical
  let B := (Pi.basis fun _ : ι => embeddingBasisOfTotallyComplex E).map (piSwapEquiv E ι)
  have hB : ∀ k, B k = coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) := by
    rintro ⟨i, j⟩
    funext w i'
    simp only [B, Basis.map_apply, Pi.basis_apply, coordEmbed_apply]
    show (Pi.single i (embeddingBasisOfTotallyComplex E j) : ι → InfinitePlace E → ℂ) i' w = _
    by_cases h : i' = i
    · subst h
      simp [embeddingBasisOfTotallyComplex_apply]
    · simp [Pi.single_eq_of_ne h]
  refine ⟨?_, ?_⟩
  · have hli := B.linearIndependent
    rwa [show (⇑B) = fun k => coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) from
      funext hB] at hli
  · rw [finrank_eq_card_basis B, finrank_eq_card_basis (Pi.basis fun _ : ι => integralBasis E)]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
