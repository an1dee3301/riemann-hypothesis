module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
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
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StMoves

variable {D : D7}


set_option maxHeartbeats 1600000 in
theorem mem_latV_iff_latLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (y : Fin V.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v := by
  rw [GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ y hy, GlobalTheory.AdelicU.mem_latHat_iff hL]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : GlobalTheory.AdelicU.vecLoc w (finPart D ∘ y) = 0 :=
      funext fun i => ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).1 (hy i)).2 w e
    rw [h0]; exact zero_mem _

theorem exists_supp_vecLoc_eq {n : ℕ} (v : Pl D) (z : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    ∃ y : Fin n → AE D, (∀ i, y i ∈ idAt D (· = v)) ∧ GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) = z := by
  choose lift hl1 hl2 using GlobalTheory.KStabBridge.exists_fin_lift (D := D)
  let y' : Fin n → Af D.host.F ⊗[D.host.F] D.host.E := fun i =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have h1 : GlobalTheory.AdelicU.vecLoc v y' = z :=
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have h2 : ∀ u, u ≠ v → GlobalTheory.AdelicU.vecLoc u y' = 0 := fun u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have h3 : finPart D ∘ (fun i => lift (y' i)) = y' := funext fun i => hl2 _
  refine ⟨fun i => lift (y' i), fun i => (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).2 ⟨hl1 _, fun w hw => ?_⟩, by rw [h3, h1]⟩
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (lift (y' i))) = 0
  rw [hl2]
  exact congrFun (h2 w hw) i


set_option maxHeartbeats 1600000 in
theorem moves_iff_stabLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (g : GA D V) :
    Moves V g L L (· = v) ↔
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
      (mt V g *ᵥ y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 *ᵥ
          GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v) := fun y hy => by
    rw [mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ g hy), GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact iff_of_eq (congrArg (· ∈ GlobalTheory.AdelicU.latLoc D.host.F L v)
      (GlobalTheory.AdelicU.vecLoc_mulVec D.sp.cm.sig V.gram v g _))
  refine Iff.trans ⟨fun h z => ?_, fun h y hy => ?_⟩ GlobalTheory.AdelicU.mem_stabLoc.symm
  · obtain ⟨y, hy, rfl⟩ := exists_supp_vecLoc_eq v z
    exact (mem_latV_iff_latLoc V L hL v y hy).symm.trans ((h y hy).trans (key y hy))
  · exact (mem_latV_iff_latLoc V L hL v y hy).trans ((h _).trans (key y hy).symm)


theorem moves_inv {V : HSp D} {g : GA D V} {L M : Lat V} {P : Pl D → Prop} (hg : Moves V g L M P) :
    Moves V g⁻¹ M L P := by
  intro y hy
  have h1 := hg (mt V g⁻¹ *ᵥ y) (GlobalTheory.FinPl.KOpen.supp_mulVec V P g⁻¹ hy)
  rw [Matrix.mulVec_mulVec, show mt V g * mt V g⁻¹ = mt V (g * g⁻¹) from rfl, mul_inv_cancel,
    show mt V (1 : GA D V) = 1 from rfl, Matrix.one_mulVec] at h1
  exact h1.symm


end GlobalTheory.StMoves

end
