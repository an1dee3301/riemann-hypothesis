module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isWeil_of_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S S' T' Tg : HSp D} (hS : S = S') (hT : Tg = T')
    {χS χT : (AE D)ˣ →* Circle} (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS χT ω') :
    ∃ ω : GlobalTheory.Grid.WRep S Tg, GlobalTheory.Grid.IsWeil ψ false S Tg χS χT ω ∧ HEq ω ω' := by
  subst hS hT
  exact ⟨ω', h, HEq.rfl⟩

theorem omCol_of_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ω ∧ HEq ω (W.om (.top t j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ t j hj
  have hS : (G.Xp j).V = G'.V (.top j) := (hSp.top j hj.le).sp
  have hT : (G.nX j).V = G'.V (.top (j + 1)) := (hSp.top (j + 1) hj).sp
  have hω := W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have hr : ∀ k, k ≤ D.R.m → Even (G'.V (.top k)).rank := fun k hk => by
    have := (G'.isV (X := .top k) hk (fun _ h => by cases h)).rank
    rw [this]; exact even_rankX D k
  have eS : G'.chrS (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrS, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr j hj.le)]
  have eT : G'.chrT (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrT, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr (j + 1) hj)]
  rw [eS, eT, hW.ψ] at hω
  exact exists_isWeil_of_eq hS hT _ hω

end GlobalTheory.GridJoin
