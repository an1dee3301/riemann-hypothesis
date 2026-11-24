module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelPlaces

open IsDedekindDomain NumberField GlobalTheory.IdemSupport

variable {D : D7} {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

theorem ev_sum {ι : Type} (s : Finset ι) (f : ι → Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (∑ i ∈ s, f i) Q = ∑ i ∈ s, Φ (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem conjPl_eq_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.DivisionValues.conjPl P = cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)

theorem under_injOn {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (h : Formalism.IndefR.Datum.IsIdemSum e P) :
    Set.InjOn (fun PP : Formalism.L2.DIV.Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (P : Set (Formalism.L2.DIV.Pl D.host.E)) := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  intro PP hPP PP' hPP' hu
  by_contra hne
  have hd : ∀ Q ∈ P, IsDelta Φ Q (es Q) := fun Q hQ => delta_of_isIdemAt hΦ (hes Q hQ)
  have hc' : PP' = cP PP := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hu.symm with h1 | h1
    · exact absurd h1.symm hne
    · rw [h1, conjPl_eq_cP]
  have hc : PP = cP PP' := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hu with h1 | h1
    · exact absurd h1 hne
    · rw [h1, conjPl_eq_cP]
  have e1 : Φ (∑ Q ∈ P, es Q) PP = 1 := by
    rw [ev_sum, Finset.sum_eq_single PP (fun Q hQ hQP => (hd Q hQ).2.2 PP (Ne.symm hQP))
      (fun h => absurd (Finset.mem_coe.1 hPP) h), (hd PP (Finset.mem_coe.1 hPP)).2.1]
  have e2 : Φ (cA D (∑ Q ∈ P, es Q)) PP = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ev_sum, Finset.sum_eq_single PP' ?_ (fun h => absurd (Finset.mem_coe.1 hPP') h)]
    · have := (delta_conj hΦ (hd PP' (Finset.mem_coe.1 hPP'))).2.1
      rwa [← hc] at this
    · intro Q hQ hQP
      refine (delta_conj hΦ (hd Q hQ)).2.2 PP fun hQc => ?_
      have hv : Q.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by rw [← under_cP Q, ← hQc]
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hv with h1 | h1
      · rw [h1] at hQc
        exact hne (hc'.trans hQc.symm).symm
      · rw [conjPl_eq_cP, ← hc'] at h1
        exact hQP h1
  have e3 := ev_mul (Φ := Φ) (∑ Q ∈ P, es Q) (cA D (∑ Q ∈ P, es Q)) PP
  rw [h0, ev_zero, e1, e2, one_mul] at e3
  exact zero_ne_one e3


end GlobalTheory.LevelPlaces
