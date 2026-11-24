module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Group

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.ratReal :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (r : FinPt G X)
      (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E), GlobalTheory.RatMoveJets.RatCoord _ (fr X) r U →
      ∃ γ ∈ GQ (G.V X), ∃ k ∈ GinfC (G.V X), (∀ x : FinPt G X, ((r * x : FinPt G X) : GA D (G.V X)) = γ * ((x : GA D (G.V X)) * k)) ∧
        GlobalTheory.DefStep.realAct W.θ fr X k⁻¹ = rhoVr (tauE D) (wt G X) (Unitary.toUnits U) := by
  intro D T L sc G W fr X r U h
  obtain ⟨γ, hγ, hf, hm⟩ := h
  have hk : γ⁻¹ * (r : GA D (G.V X)) ∈ GinfC (G.V X) := by
    show finHom (G.V X) (γ⁻¹ * (r : GA D (G.V X))) = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  refine ⟨γ, hγ, γ⁻¹ * (r : GA D (G.V X)), hk, fun x => ?_, ?_⟩
  · have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC (G.V X) hk x.2
    rw [← hc, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rfl
  · have hrat : Bridge.IsRatMat (G.V X) ⟨γ, hγ⟩ (fr X * Unitary.toUnits U * (fr X)⁻¹) := Units.ext hm
    have hin : GlobalTheory.DefStep.realIn W.θ fr X γ = embGL (tauE D) (Unitary.toUnits U) := by
      funext τ
      have h1 := GlobalTheory.CoefModel.realGL_rat W.θ_is (G.V X) ⟨γ, hγ⟩ _ hrat τ
      have h2 : GlobalTheory.DefStep.realIn W.θ fr X γ τ = (GlobalTheory.DefStep.frGL fr X τ)⁻¹ *
          GlobalTheory.CoefModel.realGL W.θ (G.V X) γ τ * GlobalTheory.DefStep.frGL fr X τ := by
        simp [GlobalTheory.DefStep.realIn]
      rw [h2, h1, map_mul, map_mul, map_inv, GlobalTheory.DefStep.frGL]
      show _ = Formalism.UG.bc (tauE D τ) (Unitary.toUnits U)
      group
    rw [_root_.mul_inv_rev, inv_inv, map_mul,
      GlobalTheory.DefStep.realAct_fin W.θ fr X (inv_mem r.2), one_mul, GlobalTheory.DefStep.realAct, MonoidHom.comp_apply,
      MonoidHom.comp_apply, hin]
    rfl
