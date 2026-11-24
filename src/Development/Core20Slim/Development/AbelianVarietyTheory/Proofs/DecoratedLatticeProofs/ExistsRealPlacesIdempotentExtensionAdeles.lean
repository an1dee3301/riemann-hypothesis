module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem realIdem_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem realIdem_gen (σ : E →ₐ[F] E) : ∃ e : AF F ⊗[F] E, e * e = e ∧ sigR (AF F) σ e = e ∧
    (∀ v, compFin F E v e = 0) ∧ (∀ w, compInf F E w e = 1) ∧
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom e = 0 ∧
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom e = 1 := by
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have h0 : sndA F (pairA F 1 0) = 0 := rfl
  have h1 : fstA F (pairA F 1 0) = 1 := rfl
  refine ⟨pairA F 1 0 ⊗ₜ[F] (1 : E), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  · exact realIdem_map F E (AlgHom.id F (AF F)) σ _
  · intro v
    refine (realIdem_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, h0, map_zero, TensorProduct.zero_tmul]
  · intro w
    refine (realIdem_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, h1, map_one, Algebra.TensorProduct.one_def]
  · rw [realIdem_map, h0, TensorProduct.zero_tmul]
  · rw [realIdem_map, h1, Algebra.TensorProduct.one_def]

end

theorem realIdem_exists : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 :=
  fun D => realIdem_gen D.host.F D.host.E _

end GlobalTheory.StdUnn
