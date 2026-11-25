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
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Linear
public import Init.Data.Int.OfNat
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.RArray
public import Init.Data.Zero
public import Init.Grind.Norm
public import Init.Grind.Ring.Basic
public import Init.Grind.Util
public import Init.GrindInstances.Ring.Int
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

theorem arrS_cast_weil_vac {D : D7} {S S' T T' : Node D} (hS : S = S') (hT : T = T') (a : ArrS S T)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) {α : Type} (ω' : α)
    (hw : IsWeil ψ false S.V T.V χS χT a.ω) (hv : IsVac ψ θ false S T a.vac) (ho : HEq a.ω ω') :
    IsWeil ψ false S'.V T'.V χS χT (a.cast hS hT).ω ∧ IsVac ψ θ false S' T' (a.cast hS hT).vac ∧
      HEq (a.cast hS hT).ω ω' := by
  subst hS hT
  exact ⟨hw, hv, ho⟩

theorem chainStepCharacters_eq_gridRowZero_ranks {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (j : ℕ) :
    Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
      (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

theorem testGridRowZeroArrows_weil_vacua_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → GlobalTheory.Grid.IsWeil R.ψ false (GlobalTheory.Grid.row0 R j).V (GlobalTheory.Grid.row0 R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (GlobalTheory.Grid.th0 R t j).ω ∧ GlobalTheory.Grid.IsVac R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac ∧ HEq (GlobalTheory.Grid.th0 R t j).ω (W.om (.mu t 0 j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ _ _ t j hj
  have hc := chainStepCharacters_eq_gridRowZero_ranks R t j
  by_cases h : j + 1 < D.R.m
  · have hw : IsWeil R.ψ false (nodeY R j).V (nodeY R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepY R t j).ω := by
      have := hR.chain.ωY t j h
      rw [hc] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R j) (nodeY R (j + 1)) (stepY R t j).vac := (hR.chain.vY t j h).1
    have key := arrS_cast_weil_vac (nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (nodeY_eq_chainVertexAtRowZero_of_lt R h) (stepY R t j) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omY t j h).symm
    unfold th0
    rw [dite_eq_left h]
    exact key
  · have h' : j + 1 = D.R.m := by omega
    have hw : IsWeil R.ψ false (nodeY R (D.R.m - 1)).V (nodeX R).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepX R t).ω := by
      have hc' : Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m =
          (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
        rw [← h']; exact hc
      have := hR.chain.ωX t
      rw [hc'] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R (D.R.m - 1)) (nodeX R) (stepX R t).vac := (hR.chain.vX t).1
    have key := arrS_cast_weil_vac (nodeY_pred_eq_chainVertexAtRowZero_last R h') (nodeX_eq_chainVertexAtRowZero_of_ge R h) (stepX R t) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omX t j h').symm
    unfold th0
    rw [dite_eq_right h, dite_eq_left h']
    exact key

end GlobalTheory.GridJoin

end
