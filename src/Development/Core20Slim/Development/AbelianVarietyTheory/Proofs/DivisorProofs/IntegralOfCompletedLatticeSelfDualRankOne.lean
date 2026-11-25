module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth

variable {D : D7}

theorem hO_single_of_gram_one {S T : HSp D} (hS : S.gram = 1) (hT : T.gram = 1) (p : Fin T.rank) (q : Fin S.rank)
    (x : AE D) (y : WO S T) : hO S T (Matrix.single p q x) y = cA D (y p q) * x := by
  unfold hO
  rw [hS, hT, inv_one, Finset.sum_eq_single q, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.single_apply_same, map_one, one_mul, mul_one]
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases h : d = p
    · subst h; simp [Matrix.one_apply_ne hb]
    · simp [Matrix.single_apply_of_row_ne (Ne.symm h)]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem fe_incA_mul (a : D.host.E) (z : AE D) : fe D (incA D a * z) = algebraMap D.host.E (FA D) a * fe D z := by
  rw [map_mul, fe_apply (incA D a), GlobalTheory.LatVac.finPart_incA, GlobalTheory.FinIdlRead.finAdEquiv_one_tmul]

theorem inHat_one_fe_iff (z : AE D) : InHat 1 (fe D z) ↔ finPart D z ∈ intAE D := by
  rw [inHat_one_iff, GlobalTheory.FinIdlRead.mem_intAE_iff_finAdEquiv]
  rfl

theorem inHat_of_char_dual : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (LB : Lat T) (n : ℕ), IsStdChar D ψ (-1) →
  S.gram = 1 → T.gram = 1 → IsSelfDualC S (stdLat S) → IsSelfDualC T LB → r ≠ 0 →
  (∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((n : D.host.E) * r) 1 u) →
  ∀ (p : Fin T.rank) (q : Fin S.rank) (c : AE D), infPart D c = 0 →
  (∀ t : AE D, infPart D t = 0 → InHat 1 (fe D t) →
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (t * c)))) = 1) →
  InHat 1 (algebraMap D.host.E (FA D) ((n : D.host.E) * n * r) * fe D c) := by
  intro D ψ S T r LB n hψ hS hT hΛS hΛT hr hL p q c hc h
  have hmem : (Matrix.single p q (incA D (n : D.host.E) * c) : WO S T) ∈
      latO S T (stdLat S) LB fun _ => True := by
    refine GlobalTheory.LatVac.mem_of_char hψ hΛS hΛT ?_ fun u' hu' => ?_
    · rw [Matrix.map_single, map_mul, hc, mul_zero, Matrix.single_zero]
    · obtain ⟨h0, h1⟩ := hL u' hu'
      have h0' : infPart D (u' p q) = 0 := congrFun (congrFun h0 p) q
      have ht := h (cA D (incA D ((n : D.host.E) * r) * u' p q))
        (by rw [(GlobalTheory.IdemSupport.parts_cA _).1, map_mul, h0', mul_zero, map_zero])
        (by
          rw [inHat_one_fe_iff]
          refine GlobalTheory.IdemSupport.finPart_cA_mem ?_
          rw [← inHat_one_fe_iff, fe_incA_mul]
          exact h1 p q)
      have e : incA D (star r⁻¹) * (cA D (incA D ((n : D.host.E) * r) * u' p q) * c) =
          cA D (u' p q) * (incA D (n : D.host.E) * c) := by
        have e1 : incA D (star r⁻¹) * incA D (star ((n : D.host.E) * r)) = incA D (n : D.host.E) := by
          rw [← map_mul, ← star_mul, mul_assoc, mul_inv_cancel₀ hr, mul_one, star_natCast]
        rw [map_mul, GlobalTheory.IdemSupport.cA_incA, ← e1]
        ring
      rw [e] at ht
      unfold symplO
      rw [hO_single_of_gram_one hS hT]
      exact ht
  have h2 := (hL _ hmem).2 p q
  rw [Matrix.single_apply_same, fe_incA_mul, ← mul_assoc, ← map_mul] at h2
  rw [mul_right_comm]
  exact h2

end GlobalTheory.CosetOrth
