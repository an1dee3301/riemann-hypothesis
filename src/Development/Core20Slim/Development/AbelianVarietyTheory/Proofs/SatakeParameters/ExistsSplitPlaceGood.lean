module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import ReciprocityTheory.Automorphisms.Unitary

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.OffBad

theorem splitPlace_of_isSplitPl (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) : ∃ s : SplitPlace D.host.E, s.w = w := by
  have hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x; rw [GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]
  have hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := by
    intro z; rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  obtain ⟨x, hx, hy⟩ := hw
  have hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w) := by
    refine ⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩
    · rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hx
    · rw [GlobalTheory.DimPartsCompare.mem_cPl] at hy'
      refine hy _ ?_ hy'
      rw [hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hsp
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have := hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])
  rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj] at this
  exact this.symm

theorem isSplitPl_of_isSplit (D : D7) (w : PlE D.host)
    (h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : IsSplitPl D.host w := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := h
  rw [GlobalTheory.Mem.GoodPlace.isSplitPl_iff]
  by_cases hw : w = P
  · refine ⟨Q, fun e => hPQ (hw.symm.trans e), ?_⟩
    ext1; exact hQ
  · refine ⟨P, hw, ?_⟩
    ext1; exact hP

end GlobalTheory.OffBad

namespace GlobalTheory.OffBad

end GlobalTheory.OffBad
