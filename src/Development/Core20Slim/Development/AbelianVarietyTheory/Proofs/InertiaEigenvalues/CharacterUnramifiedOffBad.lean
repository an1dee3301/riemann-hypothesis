module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict  
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BasePairChar

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem unrAt_of_unramAt {c : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hc : GlobalTheory.WeilParts.UnramAt ε c) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.LFun.UnrAt c w := by
  subst hw
  have key : ∀ y, Formalism.L2.Host.IsUnitAt w y → finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ) ∈ intAE D := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).2 fun P => by
      rw [show GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ)) =
        Neutral.B1.finiteSingle _ w y from GlobalTheory.LFun.finTens_locIdele w y]
      by_cases e : P = w
      · subst e; rw [GlobalTheory.LFun.finSingle_self]; exact hy.le
      · rw [GlobalTheory.LFun.finSingle_ne e, map_one]
  obtain ⟨α, rfl, h1, -⟩ := hε
  intro y hy
  have hs : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * ((GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1) =
      (GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1 := by
    refine GlobalTheory.LFun.tens_ext ?_ ?_
    · simp only [map_mul, map_sub, map_one, GlobalTheory.LFun.infTens_locIdele, sub_self, mul_zero]
    · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      have e2 := GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y
      refine FiniteAdeleRing.ext _ fun P => ?_
      simp only [map_mul, map_sub, map_one, e2]
      have hA : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.LFun.finTens D.host.F D.host.E
          (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) =
          GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) := rfl
      rw [hA]
      change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) P *
          (Neutral.B1.finiteSingle D.host.E w y P - 1) = Neutral.B1.finiteSingle D.host.E w y P - 1
      rw [GlobalTheory.LFun.finAdEquiv_tmul, map_one, mul_one]
      by_cases hP : P = w
      · subst hP
        rw [GlobalTheory.LFun.finSingle_self]
        have : α (P.under (𝓞 D.host.F)) = 1 := h1
        rw [this, map_one, one_mul]
      · rw [GlobalTheory.LFun.finSingle_ne hP, sub_self, mul_zero]
  have h := hc _ hs (key y hy) (by
    rw [← map_inv]
    refine key _ ?_
    unfold Formalism.L2.Host.IsUnitAt at hy ⊢
    rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  exact (congrArg Circle.toUnits h).trans (map_one _)


end GlobalTheory.BasePairChar
