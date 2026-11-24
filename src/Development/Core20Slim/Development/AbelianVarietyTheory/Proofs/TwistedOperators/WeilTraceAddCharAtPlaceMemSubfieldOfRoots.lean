module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.FunObj

theorem psiAt_mem_subfield_of_roots : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}, (∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) → HasConductor (psiAt W w) 1 → ∀ (x : Kw w), valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1 → (psiAt W w x : ℂ) ∈ F := by
  intro D T L sc G F W w hF hc x hx
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  set q := Ideal.absNorm w.asIdeal
  set n := depthAt G w
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : psiAt W w ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  apply hF
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]

end GlobalTheory.FunObj
