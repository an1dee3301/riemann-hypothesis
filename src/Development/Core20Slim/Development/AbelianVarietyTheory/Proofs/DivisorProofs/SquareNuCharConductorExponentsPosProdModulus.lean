module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareNuHeckeCharacterNotUnramifiedAtChosenPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
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
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SqTop.CondExpo

theorem levelLe_of_le {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)}
    {a b : ℕ} (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

theorem expAt_succ {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (h : χ.LevelLe v (n + 1)) (h' : ¬ χ.LevelLe v n) : GlobalTheory.CMVal.ExpAt χ v (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.SqTop.CondExpo


open GlobalTheory.SqTop.CondExpo in
theorem GlobalTheory.SqTop.CondExpo.expo_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), (∀ w ∈ locPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w (c w)) →
    (∀ w ∈ locPl G t, 1 ≤ c w) ∧ modul (locPl G t) c = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hμ := L.C.isMu0 j
  have enu : nuH G t i j = L.C.mu0 j * L.xiH t * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, div_eq_mul_inv]
  have echi : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [enu, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

  have hW : ∀ v ∈ G.pl.S0, GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) (SqNum.condExp G.pl v) := by
    intro v hv
    have hu := G.pl.under_w hv
    by_cases h0 : v = G.pl.v0
    · subst h0
      rw [SqNum.condExp, if_pos rfl]
      refine expAt_succ (n := 0) ?_ ?_
      · rw [enu]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul (G.ch.lev0 _ k1 k2 _ hu).1.inv
      · intro h
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
    · have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
      rw [SqNum.condExp, if_neg h0]
      have hl := G.ch.lev1 _ k1 k2 (G.pl.w v) (by rw [hu]; exact h1)
      refine expAt_succ (n := 1) ?_ ?_
      · rw [enu]
        exact ((levelLe_of_le (hμ.tame _) (by omega)).mul (levelLe_of_le (hL.xi_tame t _) (by omega))).mul hl.1.inv
      · intro h
        apply hl.2
        rw [echi]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul h.inv

  have hQ : ∀ w ∈ twPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w 1 := by
    intro w hw
    have hw' : w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
      simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
      exact ⟨hw.1.resolve_left hw.2, hw.2⟩
    have hS1 : w.under (𝓞 D.host.F) ∉ S1 D := fun h => by
      refine hw'.2 ?_
      rw [G.pl.w_Q t w hw'.1 h]
      exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
      (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t w hw'.1) hS1
    refine expAt_succ (n := 0) ?_ ?_
    · rw [enu]
      exact ((hμ.tame _).mul (hL.xi_tame t _)).mul
        (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 w hS0) 1).inv
    · intro h
      exact GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j w hw ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  have cW : ∀ v ∈ G.pl.S0, c (G.pl.w v) = SqNum.condExp G.pl v := fun v hv =>
    (hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv))).unique (hW v hv)
  have cQ : ∀ w ∈ twPl G t, c w = 1 := fun w hw =>
    (hc w (Finset.mem_filter.1 hw).1).unique (hQ w hw)
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [cW v hv, SqNum.condExp]
      split_ifs <;> omega
    · rw [cQ w (Finset.mem_filter.2 ⟨hw, h⟩)]
  · rw [modul, modT, ← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0)]
    have e1 : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.W0 := by
      ext w
      simp only [Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union]
      tauto
    have e2 : (locPl G t).filter (fun w => w ∉ G.pl.W0) = twPl G t := rfl
    rw [e1, e2]
    congr 1
    · rw [Places.W0, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
      exact Finset.prod_congr rfl fun v hv => by rw [cW v hv]
    · exact Finset.prod_congr rfl fun w hw => by rw [cQ w hw, pow_one]

end
