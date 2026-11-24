module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelFlatMapFourierJacobiStep
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastBiExpand
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
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
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastTwoSteps_localModel_flatMap_fourierJacobiStep : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hLoc : LocP ch) (hBes : BesP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (r r₀ h : Pts ch.G)
    (hpts : IsPts ch t w β p.e r r₀ h) (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt ch.G j 0 hj))
    (h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1))
    (h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j)),
    ∃ (F₀ : Frame (Kw w) (besAt ch.G hM j 0 hj vN).V₀.rank (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit))
      (T₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) →ₗ[ℂ]
        (WO (besAt ch.G hM j 0 hj vN).V₀ (ch.G.V (.top (j + 1))) → ℂ)),
      p.IsCoreFrame (besAt ch.G hM j 0 hj vN) (p.xi ^ 0)⁻¹ (frTop ch.S.toGridChoice t w j (by omega)) F₀ ∧
      p.IsModel ch.W.ψ F₀ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) T₁ ∧
      (∀ O, IsOne O → T₁ O = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
        ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r₀) j, 1) (v ⟨j, by omega⟩))) ∧
      ∃ Φ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)),
        Φ.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (datC h₁ h₂
          (phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j))) ∧
        T₁ Φ = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
          ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r) j, 1) (f ⟨j, by omega⟩)) := by
  first | exact @GlobalTheory.LastStepOne.first_step_flat | exact GlobalTheory.LastStepOne.first_step_flat | (intros; apply GlobalTheory.LastStepOne.first_step_flat <;> assumption)
