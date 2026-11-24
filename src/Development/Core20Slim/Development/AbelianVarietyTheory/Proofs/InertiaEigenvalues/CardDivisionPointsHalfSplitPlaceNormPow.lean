module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PtStringAllOfHypotheses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.DivPtLocal



theorem isSplit_of_isIdemAt : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) := by
  intro D P e he
  rw [GlobalTheory.PtString.isSplit_iff_conj, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  intro h
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he (IsDedekindDomain.HeightOneSpectrum.ext h)



end GlobalTheory.DivPtLocal
