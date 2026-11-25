module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Rat.Basic
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory

namespace GlobalTheory.VolRatioCheck

theorem embOf_mem (D : D7) (ρ : D.what₂.Tau) :
    embOf D ρ ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau ρ).2

theorem place_injective (D : D7) :
    Function.Injective fun ρ : D.what₂.Tau => InfinitePlace.mk (embOf D ρ) := by
  intro ρ ρ' h
  have hb := (factEmb D.R D.host).1
  rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
  · exact D.eTau.injective (Subtype.ext (hb.1 h1))
  · exfalso
    have e1 := embOf_mem D ρ
    have e2 := embOf_mem D ρ'
    rw [← h1] at e2
    exact (D.host.der.cmType.1 _).1 e1 e2

theorem place_bijective (D : D7) :
    Function.Bijective fun ρ : D.what₂.Tau => InfinitePlace.mk (embOf D ρ) := by
  have h1 : Nat.card D.what₂.Tau = D.R.f := by
    rw [Nat.card_congr D.eTau]; exact (factCardPsi D.R D.host).1
  have h2 : Nat.card (InfinitePlace D.host.E) = D.R.f := by
    rw [Nat.card_eq_fintype_card]; exact fDeg_host D
  exact (place_injective D).bijective_of_nat_card_le (by omega)

end GlobalTheory.VolRatioCheck

end
