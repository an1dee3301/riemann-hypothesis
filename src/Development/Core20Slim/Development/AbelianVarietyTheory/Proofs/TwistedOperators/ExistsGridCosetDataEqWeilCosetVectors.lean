module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HomLatticeCosetIndicatorPrimePowersIntegralCosetStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomLatticeCosetIndicatorEqLatticeHomCosetStatement
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
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
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
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
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

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isThetaAt_unique {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ}
    {f₀ Φ f f' : Mx D m n → ℂ} (h : IsThetaAt ψ B hs e Λ c f₀ Φ f) (h' : IsThetaAt ψ B hs e Λ c f₀ Φ f') : f = f' := by
  obtain ⟨⟨T, hT⟩, h1⟩ := h
  exact (h1 T hT).trans (h'.2 T hT).symm

theorem exists_cosetVec_of_match {D : D7} {S T : Grid.Node D} {V₁ V₂ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin V₂.rank → D.host.E)}
    {I I' : Ideal (𝓞 D.host.E)} {e : AE D} {ψ ψ' : AddChar (AF D.host.F) ℂ}
    (hS : S.V = V₁) (hT : T.V = V₂) (hΛ₁ : HEq S.Λ Λ₁) (hΛ₂ : HEq T.Λ Λ₂) (hI : I = I') (hψ : ψ = ψ')
    (vac : WO (negSp V₁) V₂ → ℂ) (cv : Cos Λ₁ Λ₂ I' → WO (negSp V₁) V₂ → ℂ)
    (hcv : ∀ κ : Cos Λ₁ Λ₂ I', IsThetaAt ψ (symplO (negSp V₁) V₂) (heisO ψ (negSp V₁) V₂) e
      (latO (negSp V₁) V₂ (Λ₁ : Set _) (Λ₂ : Set _) fun _ => True) 1 vac (cosInd e κ) (cv κ))
    (hA : ∀ c : Grid.Coset S T I, ∃ κ : Cos S.Λ T.Λ I, Grid.cosetInd S T e I c = cosInd e κ)
    (hB : ∀ κ : Cos S.Λ T.Λ I, ∃ c : Grid.Coset S T I, Grid.cosetInd S T e I c = cosInd e κ)
    (f : WO S.V T.V → ℂ) (hf : HEq f vac) :
    ∃ v : Grid.Coset S T I → (WO S.V T.V → ℂ), (∀ c, Grid.IsCosetVec ψ' true S T e I c f (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (cv κ)) ∧ ∀ κ, ∃ c, HEq (v c) (cv κ) := by
  subst hS hT hI hψ
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₂
  obtain rfl := eq_of_heq hf
  choose κ hκ using hA
  refine ⟨fun c => cv (κ c), fun c => ?_, fun c => ⟨κ c, HEq.rfl⟩, fun κ' => ?_⟩
  · show IsThetaAt ψ _ _ e _ 1 f (Grid.cosetInd S T e I c) (cv (κ c))
    rw [hκ c]
    exact hcv (κ c)
  · obtain ⟨c, hc⟩ := hB κ'
    refine ⟨c, heq_of_eq ?_⟩
    have h1 := hcv (κ c)
    have h2 := hcv κ'
    rw [← hκ c, hc] at h1
    exact isThetaAt_unique h1 h2

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isFrame_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hR : GlobalTheory.Hk3.Core R F) {G : GlobalTheory.Grid.GridPre R} (hsp : G.IsSpaces) {i : ℕ} (hi : i ≤ D.R.m) :
    Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
  cases i with
  | zero =>
    obtain ⟨c, hc⟩ := hR.lev.βY 0 (by have := D.R.two_le_m; omega)
    exact hc.1
  | succ k =>
    obtain ⟨c, hc⟩ := (hsp.vert k 0 hi (Nat.zero_le _)).frame
    exact hc.1

theorem exists_cosData_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hR hsc G' W hW G hsp hch hag hcos i hi f hf
  have hA := GlobalTheory.T.homLatticeCosetIndicator_primePowers_integralCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  have hB := GlobalTheory.T.exists_homLatticeCosetIndicator_eq_latticeHomCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  exact exists_cosetVec_of_match (I := G.lvl R) (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).sp
    (hag.vert i 0 hi.le (Nat.zero_le _)).sp (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).lat
    (hag.vert i 0 hi.le (Nat.zero_le _)).lat hag.lvl hW.ψ (W.vac i) (W.cosVec i) (hcos i hi) hA hB f hf

end GlobalTheory.GridJoin
