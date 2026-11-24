module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedUnitariesMovingBottomTriplesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScaleStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondEqMovedBottomDatumStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleBasisChangeFactorMemFieldStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleWeilMoveRightTranslateStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem frames_transfer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro D T L sc G W S _ μ₀ hL hN i j A A' WW X Y hX hY
  choose g g' h x x' y hE using fun t => GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples W i j A A' WW X Y hX hY t
  have hC := fun t => GlobalTheory.T.definite_bottom_triple_basis_change_factor_mem_field W S μ₀ hL hN i j A A' WW Y hY t (g t) (g' t) (h t) (x t) (x' t) (y t)
    (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2 (hE t).2.2.1.1 (hE t).2.2.1.2.1
    (hE t).2.2.1.2.2
  choose z hz using hC
  have κne : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have κne' : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have lA := GlobalTheory.BotFrames.isStd_lat_eq hX.std hY.std
  have lA' := GlobalTheory.BotFrames.isStd_lat_eq hX.std' hY.std'
  have lW := GlobalTheory.BotFrames.isStd_lat_eq hX.stdW hY.stdW
  refine ⟨GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)),
    ⟨hY.rank, hY.rank', hX.std, hX.std', hX.stdW, ?_⟩, rfl, rfl, rfl, fun c hc => ?_⟩
  · have hi := hY.is
    refine ⟨hi.rank, hX.is.rigA, hX.is.rigA', hX.is.rigW, hi.weil, hi.weil', ?_, ?_, hi.idem, hi.expo,
      fun t => GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale W i j A A' WW X Y hX hY t (g t) (h t) (x t) (y t) (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.2.1.1
        (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.1,
      fun t => GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum W i j A A' WW X Y hX hY t (g' t) (h t) (x' t) (y t) (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2
        (hE t).2.2.1.1 (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.2, hi.meas, hi.meas'⟩
    · show IsVacO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ Y.vac
      rw [sA, sW, lA, lW]
      exact hi.isVac
    · show IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ Y.vac'
      rw [sA', sW, lA', lW]
      exact hi.isVac'
  · refine ⟨fun t => (z t)⁻¹, ?_⟩
    have hD := GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate W i j A A' WW X Y hX hY g g' h _ _ κne κne' (fun t => ⟨(hE t).1.1, (hE t).1.2.1⟩)
      (fun t => ⟨(hE t).2.1.1, (hE t).2.1.2.1⟩) (fun t => ⟨(hE t).2.2.1.1, (hE t).2.2.1.2.1⟩) c hc
    convert hD using 2 with t
    rw [map_units_inv, hz t, inv_div]

end GlobalTheory.BotFrames

end
