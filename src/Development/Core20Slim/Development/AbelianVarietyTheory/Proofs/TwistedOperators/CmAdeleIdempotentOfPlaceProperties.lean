module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
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
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem idem_eq_locIdem (D : D7) (p : Place D) : idem D p = GlobalTheory.LocWeil.idem D p := by
  rcases p with v | τ
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl]
    rfl
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inr]
    simp only [idem, GlobalTheory.LocWeil.PlaceIdem.eInf]
    congr 2

theorem idem_spec : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  intro D
  have hE : ∀ p, idem D p = GlobalTheory.LocWeil.idem D p := idem_eq_locIdem D
  obtain ⟨hOrth, hTheta, hFinInf, hSum, -, -⟩ := GlobalTheory.LocWeil.PlaceIdem.idem_props D
  simp only [hE]
  refine ⟨fun p => GlobalTheory.LocWeil.idem_mul_self p, fun p q hpq => hOrth p q hpq, fun p => GlobalTheory.LocWeil.cA_idem p,
    ?_, hFinInf, hSum, ?_⟩
  · intro v
    rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl, GlobalTheory.LocWeil.PlaceIdem.infPart_algebraMap,
      GlobalTheory.LocWeil.PlaceIdem.finPart_algebraMap]
    refine ⟨?_, ?_, ⟨singleV D.host.F v 1, rfl, GlobalTheory.LocWeil.PlaceIdem.evalV_single_same _ v,
      fun v' h => GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h⟩⟩
    · exact TensorProduct.zero_tmul _ _
    · apply AddSubgroup.subset_closure
      refine ⟨singleV D.host.F v 1, ?_, 1, ?_⟩
      · simp only [intAf, Set.mem_setOf_eq]
        intro u
        rcases eq_or_ne u v with rfl | h
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_same]
          exact one_mem _
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h]
          exact zero_mem _
      · rfl
  · intro θ hθ τ
    refine ⟨?_, fun τ' h => ?_⟩
    · rw [hTheta θ hθ τ τ, if_pos rfl]
    · rw [hTheta θ hθ τ' τ, if_neg (Ne.symm h)]

end GlobalTheory.PlaceTensor
