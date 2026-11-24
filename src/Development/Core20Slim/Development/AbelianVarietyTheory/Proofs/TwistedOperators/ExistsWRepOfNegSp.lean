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
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
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
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
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

variable {D : D7}

theorem exists_wRep_of_negSp {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χS χT om) :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ true S T χS χT ω ∧ HEq (ω.toSgn true) om := by
  subst hS; subst hT
  let ω : GlobalTheory.Grid.WRep S T :=
    om.comp (((GlobalTheory.Grid.ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _) :
      GA D S × GA D T →* GA D (negSp S) × GA D T))
  have e : ω.toSgn true = om := MonoidHom.ext fun _ => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  show IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (ω.toSgn true)
  rw [e]
  exact h

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

theorem exists_omX_of_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V, GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω ∧ HEq (ω.toSgn true) (W.om (.chi i j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hG _ hsp _ i j hi hj
  have hv1 := (hsp.vert (i + 1) j (by omega) hj).sp
  have hv0 := (hsp.vert i j (by omega) hj).sp
  have hom := W.om_is (.chi i j) ⟨by omega, hj⟩
  rw [hW.ψ] at hom
  obtain ⟨ω, h1, h2⟩ := exists_wRep_of_negSp hv1 hv0 R.ψ _ _ (W.om (.chi i j)) hom
  refine ⟨ω, ?_, h2⟩
  have hchi : G.chi (D.R.m - i) = G'.ch.chi (D.R.m - i) := hsp.chi _ (by omega) (by omega)
  have rS : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← hv1]; exact (hG.vert i j (by omega) hj).rank
  have rT : (G'.V (.grid i j)).rank = rkV D i j := by
    rw [← hv0]
    cases i with
    | succ k => exact (hG.vert k j (by omega) hj).rank
    | zero =>
      rw [hv0]
      show (columnBlock R.toLevCh j).sp.rank = _
      simp only [rkV, zero_mul, add_zero]
      rcases hj.eq_or_lt with rfl | hk
      · rw [colY_m]; exact D.sp.X'_rank
      · rw [colY_lt _ hk]
        exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  have cS : G'.chrS (.chi i j) = G.chiAt (D.R.m - i) (rkV D (i + 1) j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid (i + 1) j)).rank = _
    rw [rS, ← hchi]
  have cT : G'.chrT (.chi i j) = G.chiAt (D.R.m - i) (rkV D i j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid i j)).rank = _
    rw [rT, ← hchi]
  rw [cS, cT] at h1
  exact h1

end GlobalTheory.GridJoin
