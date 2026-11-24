module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemPairCpt

open GlobalTheory.StdFrames

theorem cpt_sg_eq_one_of_cP_mem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∈ P) : cpt (D := D) w (sg D (toEAf D e)) = 1 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (1 - toEAf D e) = 0 := by
    rw [map_sub, map_one, GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, sub_self]
  have h2 := cpt_sg_eq_zero h1
  rw [map_sub, map_one, map_sub, map_one] at h2
  exact (sub_eq_zero.mp h2).symm

theorem cpt_sg_eq_zero_of_cP_notMem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∉ P) : cpt (D := D) w (sg D (toEAf D e)) = 0 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (toEAf D e) = 0 := by
    rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw]
  exact cpt_sg_eq_zero h1

theorem cpt_add_cA_idemSum : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := by
  intro D e P he w
  have hsplit : GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) =
      cpt (D := D) w (toEAf D e) + cpt (D := D) w (sg D (toEAf D e)) := by
    rw [map_add (f := _), toEAf_cA, map_add (f := _)]
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · rw [hsplit]
    by_cases hw : w ∈ P
    · have hc : GlobalTheory.IdemSupport.cP w ∉ P := fun hc => GlobalTheory.IdemSumBranch.conjPrime_ne he hc hw rfl
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, cpt_sg_eq_zero_of_cP_notMem he w hc, add_zero]
    · have hc : GlobalTheory.IdemSupport.cP w ∈ P := h.resolve_left hw
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw, cpt_sg_eq_one_of_cP_mem he w hc, zero_add]
  · rw [hsplit, GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg h1, cpt_sg_eq_zero_of_cP_notMem he w h2, add_zero]

end GlobalTheory.IdemPairCpt
