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
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatVac

theorem heis_at_local_identity : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (γ : W) (f : (κ → Fv F v) → ℂ) (χ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (co.rho ψ γ) f (χ • f) →
    ∀ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r → ∀ x₀, r x₀ ≠ 0 →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = χ * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f χ hγ hA r hr x₀ hx₀ ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : r x = r x₀ := hr.1 x₀ z hzat
  have hrx1 : r (x + (co.e γ).1) = r x := hr.1 x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun (hA r hr) x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add (f := _), map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : r x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  simp only [Pi.smul_apply, smul_eq_mul] at this
  apply mul_right_cancel₀ hr0
  rw [← this]
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

end GlobalTheory.LatVac
