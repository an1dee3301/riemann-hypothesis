module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOverPlace

theorem unrAt_of_unramAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F),
    IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  intro D χ v ε hε hu w hw x hx
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w x).1 hx
  have hc := GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E)
  obtain ⟨k0, k1, -⟩ := GlobalTheory.CMPrimeIdele.place_comp hc hε
  have key : χ (GlobalTheory.LFun.locIdele D.host.F w x) = 1 := by
    refine hu _ ?_ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w x).2 h1) (by
      rw [← map_inv]; exact (GlobalTheory.LFun.EulerTie.locIdele_int_iff w x⁻¹).2 h2)
    refine hc.ext' ?_ fun Q ↦ ?_
    · have k0' : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) ε) = 0 := k0
      have k2 : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) = 0 := by
        rw [map_sub, (GlobalTheory.LFun.EulerTie.parts_locIdele w x).1, map_one, sub_self]
      rw [map_mul, k0', zero_mul, k2]
    · rw [GlobalTheory.CMPrimeIdele.ev_mul]
      by_cases hQ : Q = w
      · subst hQ
        rw [k1 Q hw, one_mul]
      · have e : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) Q = 0 := by
          rw [map_sub, map_one]
          show GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (GlobalTheory.LFun.locIdele D.host.F w x : AE D) Q - 1 = 0
          rw [GlobalTheory.LFun.EulerTie.finComp_locIdele_ne hQ, sub_self]
        rw [e, mul_zero]
  show Circle.toUnits (χ (GlobalTheory.LFun.locIdele D.host.F w x)) = 1
  rw [key, map_one]

end GlobalTheory.UnrOverPlace
