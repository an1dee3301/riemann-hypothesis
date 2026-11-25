module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
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
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.TensorProduct.Basic
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
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_half (v : HeightOneSpectrum (𝓞 F)) (x c : E) :
    compFin F E v (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] c) = (1 : Fv F v) ⊗ₜ[F] x := by
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    change evalV F v (1 : Af F) = 1; exact map_one _
  have h0 : evFin F v (pairA F 1 0) = 0 := by
    change evalV F v (0 : Af F) = 0; exact map_zero _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, add_zero]

theorem compInf_half (w : InfinitePlace F) (x : E) :
    compInf F E w (2 * (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E))) = 1 := by
  have h1 : evInf F w (pairA F 0 1) = 0 := by
    change GlobalTheory.AutFunCompare.evW w (0 : Ainf F) = 0; exact map_zero _
  have h0 : evInf F w (pairA F 1 0) = 1 := by
    change GlobalTheory.AutFunCompare.evW w (1 : Ainf F) = 1; exact map_one _
  rw [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, two_mul, map_add (f := _), map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, zero_add,
    ← TensorProduct.tmul_add, add_halves, ← Algebra.TensorProduct.one_def]

theorem sigR_half (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] σ x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E) := by
  have h2 : σ (1 / 2 : E) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h2]

theorem half_add (x y : E) (h : x + y = 1) :
    (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      (1 : AF F ⊗[F] E) := by
  have hae : pairA F 0 1 + pairA F 1 0 = (1 : AF F) := Prod.ext (zero_add 1) (add_zero 1)
  rw [show (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] (x + y) + pairA F 1 0 ⊗ₜ[F] (1 / 2 + 1 / 2 : E) by
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel,
    h, add_halves, ← TensorProduct.add_tmul, hae, Algebra.TensorProduct.one_def]

end General

theorem exists_halfData : ∀ D : D7, ∃ t : AE D, HalfData t := by
  intro D
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram D.host.E D.sp.cm.cmUnram
  refine ⟨pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t₀ : D.host.E) + pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 / 2 : D.host.E),
    ?_, fun v => ?_, fun w => compInf_half w _⟩
  · exact (congrArg _ (sigR_half D.sp.cm.sig _)).trans (half_add _ _ ht₀)
  · rw [compFin_half]
    exact tmul_mem_intLoc (one_mem _) t₀

end GlobalTheory.StdUnn
