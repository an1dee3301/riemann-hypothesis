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
public import Development.Core20Slim.Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.HalfUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem mx_eq_of_nsmul_eq_of_ne_zero {D : D7} {m n : ℕ} (c : ℕ) (hc : c ≠ 0) {x y : Mx D m n}
    (h : c • x = c • y) : x = y := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply] at h1
  have hF : ((c : ↥D.host.F)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [← Nat.cast_smul_eq_nsmul (↥D.host.F), ← Nat.cast_smul_eq_nsmul (↥D.host.F)] at h1
  calc x i j = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • x i j) := (inv_smul_smul₀ hF _).symm
    _ = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • y i j) := by rw [h1]
    _ = y i j := inv_smul_smul₀ hF _

theorem UpperTheory.WildA.depthDrop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p) (l : ℕ), l.Prime → (∀ w ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ k : ℕ, 0 < k → IsCosetDatum k d → ∃ k' : ℕ, 0 < k' ∧ ¬ l ∣ k' ∧ IsCosetDatum k' d := by
  intro D T L sc G t p d l hl hP k hk hcos
  obtain ⟨x₀, hx₀, hkx, hfn⟩ := hcos
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' l hl.one_lt.ne'
  have hc : ∀ w ∈ d.P, (((l ^ a : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro w hw h
    rw [Nat.cast_pow] at h
    exact hP w hw (w.isPrime.mem_of_pow_mem _ h)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hhalf : ∀ (c : ℕ) (u : Mx D (G.pT p).rank (G.pS p).rank), IsHalf d.e u → IsHalf d.e (c • u) := by
    intro c u hu i j
    simp only [Matrix.smul_apply, mul_smul_comm, hu i j]
  obtain ⟨v, hvL, hvH, hv⟩ :=
    UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc _ hkx (hhalf _ _ hx₀)
  have hmx : m • x₀ = v := by
    apply mx_eq_of_nsmul_eq_of_ne_zero (l ^ a) (pow_ne_zero _ hl.ne_zero)
    rw [hv, smul_smul]
  refine ⟨m, hm0, hm, x₀, hx₀, by rw [hmx]; exact hvL, ?_⟩
  rw [hfn]
  congr 1
  ext x
  simp only [GlobalTheory.RowTest.halfCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, huH, rfl⟩
    refine ⟨(l ^ a) • u, AddSubgroup.nsmul_mem _ hu _, hhalf _ _ huH, ?_⟩
    rw [smul_smul, mul_comm m]
  · rintro ⟨u, hu, huH, rfl⟩
    obtain ⟨u', hu', hu'H, rfl⟩ := UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc u hu huH
    exact ⟨u', hu', hu'H, by rw [smul_smul, mul_comm m]⟩
