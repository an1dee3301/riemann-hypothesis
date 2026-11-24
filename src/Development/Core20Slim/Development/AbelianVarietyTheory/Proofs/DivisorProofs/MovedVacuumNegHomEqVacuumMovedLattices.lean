module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
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
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

private theorem isVacO_move {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS MS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT MT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLS : IsSelfDualC S LS) (hMS : IsSelfDualC S MS) (hLT : IsSelfDualC T LT) (hMT : IsSelfDualC T MT)
    (g : GA D S) (hg : g ∈ GfC S) (h : GA D T) (hh : h ∈ GfC T)
    (mg : GlobalTheory.FinPl.Moves S g LS MS (fun _ => True)) (mh : GlobalTheory.FinPl.Moves T h LT MT (fun _ => True))
    (f : WO S T → ℂ) (hf : IsVacO ψ θ S T sS sT LS LT f) : IsVacO ψ θ S T sS sT MS MT (om (g, h) f) := by
  have hθ : IsInfFam θ := hf.2.inf
  refine GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ g h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul]) (fun u => ?_) f hf
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hLS hMS hLT hMT mg mh
  have back : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
    have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ u
    rwa [inv_inv, inv_inv] at this
  refine ⟨fun hu => ⟨actO S T g⁻¹ h⁻¹ u, (key _).2 (by rwa [back]), back.symm⟩, ?_⟩
  rintro ⟨u₀, hu₀, rfl⟩
  exact (key _).1 hu₀

theorem _root_.GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    IsVacO ψ θ (neg A) WW (fun τ => -(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s τ) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mg mg' mh t₀ r r' hr hrt hrt'
  have hWd : IsWeilDatumO ψ (neg A) WW _ _ ((Y.ω t₀).toSgn true) := hY.weil t₀
  have hg₁ : (GlobalTheory.Grid.ofSgn true A).symm g ∈ GfC (neg A) := hg
  have mg₁ : GlobalTheory.FinPl.Moves (neg A) ((GlobalTheory.Grid.ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mg
  have key := isVacO_move ψ θ (neg A) WW _ _ ((Y.ω t₀).toSgn true) hWd (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ ΛA Y.rW.Λ ΛW
    (GlobalTheory.RowTest.isSelfDualC_neg' hY.rigA.1) (GlobalTheory.RowTest.isSelfDualC_neg' hA) hY.rigW.1 hW
    ((GlobalTheory.Grid.ofSgn true A).symm g) hg₁ h hh mg₁ mh Y.vac hY.isVac
  have e : ((Y.ω t₀).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm g, h) Y.vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e] at key
  have e1 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.s = Y.rA.s := rfl
  have e2 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.s = Y.rW.s := rfl
  have e3 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ = ΛA := rfl
  have e4 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ = ΛW := rfl
  have e5 : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac = Y.ω t₀ (g, h) Y.vac := rfl
  rw [e1, e2, e3, e4, e5]
  exact key
