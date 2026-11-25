module

public import Mathlib
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
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
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
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

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelTest

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)



section Unif

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}





end Unif





theorem comp_map {F E : Type} [Field F] [Field E] [Algebra F E] {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    [CommRing R''] [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (z : R ⊗[F] E) :
    Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) z =
      Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]


set_option maxHeartbeats 1000000 in
theorem charUnramAt_of {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) : CharUnramAt D χ v := by
  have kf : ∀ w (z : AE D), GlobalTheory.AdelicU.compFin D.host.F D.host.E w z = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) :=
    fun w z => comp_map _ _ z
  have ki : ∀ w (z : AE D), infPart D z = 1 → GlobalTheory.AdelicU.compInf D.host.F D.host.E w z = 1 := fun w z hz =>
    (comp_map _ _ z).trans ((congrArg (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)) hz).trans
      (map_one _))
  have kint : ∀ y ∈ intAE D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨α, hα, x, rfl⟩ := hy; exact GlobalTheory.AdelicU.tmul_mem_intLoc (hα v) x
    | zero => rw [RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy
  have kin : ∀ z : (AE D)ˣ, finPart D (z : AE D) ∈ intAE D →
      (GlobalTheory.Doubling.unitFin D.host.F D.host.E v z).val ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun z hz =>
    Set.mem_of_eq_of_mem (s := GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) (kf v z) (kint _ hz)
  intro x h1 h2 h3 h4
  have hx : x = GlobalTheory.Doubling.ideleAt D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v x) := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun w => ?_
    · rw [GlobalTheory.Doubling.unitInf_ideleAt]
      exact Units.ext (ki w x h1)
    · by_cases hw : w = v
      · subst hw; rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
      · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne hw]
        exact Units.ext ((kf w x).trans (h2 w hw))
  rw [hx]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum D χ v _ ?_ ?_ h
  · exact kin x h3
  · rw [← map_inv]
    exact kin x⁻¹ h4

end GlobalTheory.SeeSaw.LevelTest

section
open Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.SeeSaw.BaseLatTest

end GlobalTheory.SeeSaw.BaseLatTest

end

end
