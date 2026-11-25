module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem locPl_over {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  classical
  intro w hw
  rcases Finset.mem_union.1 hw with hw0 | hwQ
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw0
    exact Or.inl ((G.pl.under_w hv).symm ▸ hv)
  · exact Or.inr ⟨w, hwQ, rfl⟩

private theorem kill_lemma' {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}
    (N : Std G Set.univ) {t : T} {e : AE D} (he : IsIdemSum e (locPl G t)) (p : Pair T) {X : Node}
    (hX : DefNode D.R.m X) : ∃ a : AE D, e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 :=
  exists_kill N (Set.mem_univ t) (FinDatum.ind G t p (locPl G t) (locPl_over G t) e he) hX

theorem mem_pairLat_iff_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ x : WO (G.pS p) (G.pT p), IsHalf e x → (x ∈ pairLat G p ↔ x ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) := by
  intro D T L sc G W S t p hp e he x hx
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hXS : DefNode D.R.m (.grid (i + 1) D.R.m) := ⟨hi, rfl⟩
    have hXT : DefNode D.R.m (.grid i D.R.m) := ⟨by omega, rfl⟩
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.chi i D.R.m) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.chi i D.R.m) hXT
    refine (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) D.R.m)).1) (S.N.u (.grid i D.R.m)).1
      ?_ ?_ hT1 hT2 ha hb ?_ hhb hx).symm
    · intro v hv
      have h := hS1 v hv
      rw [← mt_negGA] at h
      exact h
    · intro v hv
      have h := hS2 v hv
      rw [← mt_negGA, map_inv] at h
      exact h
    · unfold SuppAt at hga ⊢
      rw [← mt_negGA] at hga
      exact hga
  | top t' j =>
    have hXS : DefNode D.R.m (.top j) := by simp only [DefPair] at hp; show j ≤ D.R.m; omega
    have hXT : DefNode D.R.m (.top (j + 1)) := hp
    obtain ⟨hS1, hS2⟩ := hat_moves S.N hXS
    obtain ⟨hT1, hT2⟩ := hat_moves S.N hXT
    obtain ⟨a, ha, hga⟩ := kill_lemma' S.N he (.top t' j) hXS
    obtain ⟨b, hb, hhb⟩ := kill_lemma' S.N he (.top t' j) hXT
    exact (mem_latO_iff_of_half _ _ hS1 hS2 hT1 hT2 ha hb hga hhb hx).symm
  | mu _ _ _ => exact hp.elim
  | core _ => exact hp.elim

end GlobalTheory.StdHalfLat
