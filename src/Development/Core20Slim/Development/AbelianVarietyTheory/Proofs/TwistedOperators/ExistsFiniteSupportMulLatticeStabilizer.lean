module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TruncAway

open GlobalTheory.AdelicU

theorem exists_trunc_mul_inK : ∀ {D : D7} (V : HSp D) (L : GlobalTheory.FinPl.Lat V), L.FG → Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : GA D V), ∃ (b' : GA D V) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b' = 1) ∧ GlobalTheory.FinPl.InK V L (fun v => v ∉ S) (b'⁻¹ * b) := by
  intro D V L hfg hspan S b
  haveI : Submodule.IsLattice D.host.E L := Submodule.IsLattice.of_fg _ hfg
  haveI : Submodule.IsFullLattice D.host.E L := ⟨hspan⟩
  have hfin := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram L b)
  classical
  let P : Finset (HeightOneSpectrum (𝓞 D.host.F)) := S ∪ hfin.toFinset
  let b' : GA D V := ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram b) *
    embAt D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b)
  have hat := mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b))
  have hout : ∀ v ∉ P, proj D.sp.cm.sig V.gram v b' = 1 := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact hat.2 v hv
  have hin : ∀ v ∈ P, proj D.sp.cm.sig V.gram v b' = proj D.sp.cm.sig V.gram v b := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact proj_embAt D.sp.cm.sig V.gram P _ ⟨v, hv⟩
  have hinf : projInf D.sp.cm.sig V.gram b' = projInf D.sp.cm.sig V.gram b := by
    simp only [b', map_mul, projInf_ofInf, mem_finPts.1 hat.1, mul_one]
  refine ⟨b', P, hout, ?_, ?_⟩
  · rw [GlobalTheory.FinPl.KOpen.mem_grpAt_iff]
    refine ⟨mem_finPts.2 ?_, fun v hv => ?_⟩
    · rw [map_mul, map_inv, hinf, inv_mul_cancel]
    · have hvP : v ∈ P := Finset.mem_union_left _ (not_not.1 hv)
      rw [map_mul, map_inv, hin v hvP, inv_mul_cancel]
  · refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen V L hfg _ (mem_levelOpen.2 fun v => ?_)
    by_cases hv : v ∈ P
    · rw [map_mul, map_inv, hin v hv, inv_mul_cancel]; exact one_mem _
    · rw [map_mul, map_inv, hout v hv, inv_one, one_mul]
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))

end GlobalTheory.TruncAway

end
