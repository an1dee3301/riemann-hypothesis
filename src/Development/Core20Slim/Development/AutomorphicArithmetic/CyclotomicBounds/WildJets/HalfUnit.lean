module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.halfUnit :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (p : GlobalTheory.ChiGrid.Pair T) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ c : ℕ, (∀ w ∈ P, ((c : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ u ∈ pairLat G p, IsHalf e u → ∃ u' ∈ pairLat G p, IsHalf e u' ∧ c • u' = u := by
  intro D T L sc G p P e he c hc u hu hhalf
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hc0 : c = 0
  · subst hc0
    have hS : ∑ PP ∈ P, es PP = 0 :=
      Finset.sum_eq_zero fun PP hPP => (hc PP hPP (by simp)).elim
    have hu0 : u = 0 := by
      ext i j
      have h := hhalf i j
      rw [hS, zero_mul] at h
      exact h.symm
    subst hu0
    exact ⟨0, (pairLat G p).zero_mem, fun i j => by simp, by simp⟩
  · have hx : ((c : 𝓞 D.host.E)) ≠ 0 := by exact_mod_cast hc0
    let w : AE D := (∑ PP ∈ P, es PP) * incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹
    have hw : finPart D w ∈ intAE D := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ ?_
      intro PP hPP
      by_contra hn
      exact hc PP hPP (((hes PP hPP).2 _ hx).mpr hn)
    have h1 : incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← map_mul]
      have hce : (((c : 𝓞 D.host.E) : D.host.E)) = (c : D.host.E) := by simp
      rw [hce, inv_mul_cancel₀ (by exact_mod_cast hc0), map_one]
    have hcw : (c : AE D) * w = ∑ PP ∈ P, es PP := by
      calc (c : AE D) * w
          = (∑ PP ∈ P, es PP) * (incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D)) := by
            simp only [w]; ring
        _ = ∑ PP ∈ P, es PP := by rw [h1, mul_one]
    refine ⟨w • u, GlobalTheory.LatticeStable.smul_mem_latO _ _ _ _ _ _ w hw u hu, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm _ w, mul_assoc, hhalf i j]
    · ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rw [← mul_assoc, hcw, hhalf i j]
