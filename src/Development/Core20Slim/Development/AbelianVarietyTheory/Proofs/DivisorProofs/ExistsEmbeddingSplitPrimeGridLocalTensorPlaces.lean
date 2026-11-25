module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.AdelicU

namespace GlobalTheory.LocPlTau

theorem exists_splitPrime_locPl : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (_hL : L.Is μ₀) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)), (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) →
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → splitPrime τ = w := by
  intro D T L sc G μ₀ hL t v ⟨w, hw, hv⟩
  subst hv
  obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hex : ∃ ρ : D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F)), splitPrime ρ = w := by
    by_cases e : w = splitPrime τ
    · exact ⟨τ, e.symm⟩
    · exact (existsUnique_splitPrime_eq hc e rfl (splitPrime_under τ)).exists
  obtain ⟨ρ, hρ⟩ := hex
  exact ⟨ρ, fun w' hw' h => hρ.trans (GlobalTheory.FunObj.Good.under_injOn hL G t hw hw' h.symm)⟩

end GlobalTheory.LocPlTau
