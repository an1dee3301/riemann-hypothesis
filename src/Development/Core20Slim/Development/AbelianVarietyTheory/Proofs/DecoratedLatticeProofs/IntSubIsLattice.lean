module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitMove
variable {D : D7}

def intSub (D : D7) (n : ℕ) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) where
  carrier := intVec D n
  add_mem' := fun ha hb k => (ha k).add (hb k)
  zero_mem' := fun _ => isIntegral_zero
  smul_mem' := fun c x hx k => by
    show IsIntegral ℤ ((c : D.host.E) * x k)
    exact (RingOfIntegers.isIntegral_coe c).mul (hx k)




theorem intSub_fg (n : ℕ) : (intSub D n).FG := by
  let φ : (Fin n → 𝓞 D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E) :=
    LinearMap.pi fun i => (Algebra.linearMap (𝓞 D.host.E) D.host.E).comp (LinearMap.proj i)
  have e : intSub D n = Submodule.map φ ⊤ := by
    ext x
    constructor
    · intro hx
      refine ⟨fun i => ⟨x i, hx i⟩, trivial, ?_⟩
      funext i; rfl
    · rintro ⟨y, -, rfl⟩ i
      exact RingOfIntegers.isIntegral_coe (y i)
  rw [e]
  exact (Module.Finite.fg_top (R := 𝓞 D.host.E) (M := Fin n → 𝓞 D.host.E)).map φ


instance intSub_isLattice (n : ℕ) : Submodule.IsLattice D.host.E (intSub D n) := Submodule.IsLattice.of_fg D.host.E (intSub_fg n)







variable {S T : HSp D}

theorem isSBHalf_comp₂ {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ') {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ' Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΨ
  refine ⟨fun t ht => (GlobalTheory.SchrMove.isHalf_actO_iff g h t).1 (h1 _ ht), k, hk, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · beta_reduce
    rw [GlobalTheory.SchrMove.actO_add, GlobalTheory.SchrMove.actO_nsmul]
    exact h2 _ ((hΛ u).1 hu) (GlobalTheory.SplitHecke.isHalf_actO g h hu') _
  · rw [hΛ, GlobalTheory.SchrMove.actO_nsmul]
    exact h3 _ ht

theorem halfInd_comp₂ {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ') (t : WO S T) : halfInd e Λ' (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos ht, if_pos ⟨(hΛ t).1 ht.1, GlobalTheory.SplitHecke.isHalf_actO g h ht.2⟩]
  · rw [if_neg ht, if_neg fun h' => ht ⟨(hΛ t).2 h'.1, (GlobalTheory.SchrMove.isHalf_actO_iff g h t).1 h'.2⟩]

theorem isPlaceModel_move₂ {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D}
    {Λ Λ' : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ')
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf a Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ' 1 (om (g, h) f₀)
      (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h)) := by
  have ev : ∀ Ψ : WO S T → ℂ, (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h)) Ψ =
      om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun _ => rfl
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have s := isSBHalf_comp₂ hΛ hΨ
    have e1 := hTm.trans _ s _ (GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hx)
    have e2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ x) _ (hth _ s)
    rw [GlobalTheory.AdelicLatMove.actO_actO_inv] at e2
    rw [ev, ev, ← e2, ← e1]
    simp only [GlobalTheory.SchrMove.actO_add, GlobalTheory.AdelicLatMove.actO_actO_inv]
  · have s := isSBHalf_comp₂ hΛ hΨ
    have e1 := hTm.modul _ s _ (GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hy)
    have e2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ y) _ (hth _ s)
    rw [GlobalTheory.AdelicLatMove.actO_actO_inv] at e2
    have e3 : ∀ t, symplO S T (actO S T g h t) y = symplO S T t (actO S T g⁻¹ h⁻¹ y) := fun t => by
      rw [← GlobalTheory.SplitHecke.symplO_actO S T g h t, GlobalTheory.AdelicLatMove.actO_actO_inv]
    rw [ev, ev, ← e2, ← e1]
    simp only [e3]
  · have v := hTm.vac
    rw [one_smul] at v
    have e1 : (fun t => halfInd a Λ' (actO S T g h t)) = halfInd a Λ := funext (halfInd_comp₂ hΛ)
    rw [one_smul, ev, e1, v]

end GlobalTheory.SplitMove

namespace GlobalTheory.SplitMove


end GlobalTheory.SplitMove
