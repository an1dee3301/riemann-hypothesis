module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.AlgebraMapAEEqZero
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitOrInertP
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLinF
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemLoc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SbHalfHalfInd
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Fin.LevelGroupLemmas

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def epsP (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : AF D.host.F := ∑ PP ∈ P, sA (belowPl PP) 1

theorem sA_orth' {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) :
    sA v (1 : v.adicCompletion D.host.F) * sA w (1 : w.adicCompletion D.host.F) = 0 :=
  algebraMap_AE_eq_zero (D := D) (by rw [map_mul]; exact phiE_orth h)

section Sum

variable {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}

theorem algebraMap_epsP (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP) :
    algebraMap (AF D.host.F) (AE D) (epsP P) = e + cA D e := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [epsP, map_sum, he, map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun PP hPP => (below_of_idemAt (hes PP hPP)).symm

open Classical in
theorem single_one_mul_idempotent_eq_zero_of_notMem (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) {a : Formalism.L2.DIV.Pl D.host.E} {A : Finset (Formalism.L2.DIV.Pl D.host.E)} (ha : a ∉ A)
    (hsub : insert a A ⊆ P) : sA (belowPl a) (1 : (belowPl a).adicCompletion D.host.F) * epsP A = 0 := by
  rw [epsP, Finset.mul_sum]
  refine Finset.sum_eq_zero fun PP hPP => sA_orth' fun hv => ?_
  have := idemSum_below_inj hes he hc (hsub (Finset.mem_insert_self a A)) (hsub (Finset.mem_insert_of_mem hPP)) hv
  exact ha (this ▸ hPP)

theorem isIdempotentElem_placeIdempotent (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) : ∀ A : Finset (Formalism.L2.DIV.Pl D.host.E), A ⊆ P → IsIdempotentElem (epsP A) := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; simp [epsP, IsIdempotentElem]
  | insert a A ha ih =>
    intro hsub
    rw [epsP, Finset.sum_insert ha]
    exact isIdem_add_orth (sA_idem _) (ih ((Finset.subset_insert a A).trans hsub))
      (single_one_mul_idempotent_eq_zero_of_notMem hes he hc ha hsub)

end Sum

section Chain

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
  {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}

end Chain

theorem vacFixOff (hSL : SplitLin D) (hPM : PlaceModelAt D) (hSOI : SplitOrInert D) : VacFixOffO D :=
  vacFixOff_of hSL hPM hSOI fun _ _ _ _ _ _ _ _ hfS hfT _ _ _ _ hg hh t => actO_mem_latAll_iff hfS hfT hg hh t

end Formalism.IndefR.Fin.LevelGroupLemmas

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end
