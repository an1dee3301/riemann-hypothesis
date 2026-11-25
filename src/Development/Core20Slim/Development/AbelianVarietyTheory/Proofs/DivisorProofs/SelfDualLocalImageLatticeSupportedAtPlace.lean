module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LatVac.DualLoc

variable {F : Type} [Field F] [NumberField F]

theorem form_smul_left {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (u : AF F) (z γ : W) : B (u • z) γ = u * B z γ := by
  rw [co.form, co.form, map_smul]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]

theorem at_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (B z γ) := by
  intro u hu
  rw [smul_eq_mul, ← form_smul_left co, hz u hu, co.form]
  simp

theorem evFin_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z γ : W) :
    evFin F v (B z γ) = (GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2 := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sub, map_sum, map_mul]
  rfl

theorem psi_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) :
    ψ (B z γ) = GlobalTheory.LatVac.psiAt ψ v ((GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2) := by
  rw [GlobalTheory.VacIndic.psi_of_at ψ (at_form co v hz γ), ← evFin_form co v z γ]
  rfl

theorem map_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Λ : AddSubgroup W), (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ) →
    (∀ z : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1)) →
    ∀ w : (κ → Fv F v) × (κ → Fv F v), w ∈ Λ.map (GlobalTheory.LatVac.locCo co v) ↔
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), GlobalTheory.LatVac.psiAt ψ v (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
  intro F _ _ v W _ _ B κ _ co ψ Λ hat hdual w
  constructor
  · rintro ⟨z, hz, rfl⟩ l ⟨γ, hγ, rfl⟩
    rw [← psi_form co v ψ (hat z hz) γ]
    exact (hdual z (hat z hz)).1 hz γ hγ
  · intro hw
    obtain ⟨p, hp⟩ : ∃ p : (κ → AF F) × (κ → AF F),
        p = (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) := ⟨_, rfl⟩
    have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (co.e.symm p) := by
      intro u hu
      have hp0 : u • p = 0 := by
        subst hp
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
        · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
      rw [← map_smul, hp0, map_zero]
    have hloc : GlobalTheory.LatVac.locCo co v (co.e.symm p) = w := by
      subst hp
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · show evFin F v ((co.e (co.e.symm _)).1 k) = w.1 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
      · show evFin F v ((co.e (co.e.symm _)).2 k) = w.2 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)
    have hz : co.e.symm p ∈ Λ := (hdual _ hzat).2 fun γ hγ => by
      rw [psi_form co v ψ hzat γ, hloc]
      exact hw _ ⟨γ, hγ, rfl⟩
    exact ⟨_, hz, hloc⟩

end GlobalTheory.LatVac.DualLoc
