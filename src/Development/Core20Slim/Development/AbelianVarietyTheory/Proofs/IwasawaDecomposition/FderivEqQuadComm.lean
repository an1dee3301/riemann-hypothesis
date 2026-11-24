module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem IsQuadOf.apply_vec {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {om : V → V → ℝ} {X : V → V} {κ : Type} [Fintype κ] {c : κ → ℂ} {p q : κ → V}
    (h : IsQuadOf om X c p q) (L : V →ₗ[ℝ] B) (v : V) :
    (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) v : ℂ) • L (p i) + (om (p i) v : ℂ) • L (q i)) = L (X v) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)]
  intro φ
  have := h ((φ.restrictScalars ℝ).toLinearMap ∘ₗ L) v
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, ← mul_add] using this

theorem fderiv_eq_quad_comm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (X : V → V) (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (fun x y => om x y) X c p q → ∀ f, Sm ρ f → ∀ w, fderiv ℝ (fun u => ρ u f) w (X w) = quad ρ c p q (ρ w f) - ρ w (quad ρ c p q f) := by
  intro V _ _ B _ _ om ρ h0 hH X κ _ c p q hQ f hf w
  have C := GlobalTheory.Mem.Lift.DCalc.dH_calculus V B om ρ h0 hH
  obtain ⟨h1, h2, h3, h4, -⟩ := C f hf
  have skew : om w (X w) = - om (X w) w := by
    have := h0 (w + X w)
    simp only [map_add (f := _), _root_.add_apply, h0] at this
    linarith
  have key : ∀ u v, dH ρ u (dH ρ v (ρ w f)) = ρ w (dH ρ u (dH ρ v f))
      + (2 * π * I : ℂ) • ρ w ((om v w : ℂ) • dH ρ u f + (om u w : ℂ) • dH ρ v f)
      + ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om v w : ℂ) * (om u w : ℂ)))) • ρ w f := by
    intro u v
    obtain ⟨-, g2, -, g4, -⟩ := C _ (h1 v)
    have hs : Sm ρ ((2 * π * I * (om v w : ℂ)) • ρ w f) := (smS ρ).smul_mem _ (h2 w)
    rw [h4 v w, dH_add u (g2 w) hs, dH_smul u _ (h2 w), g4 u w, h4 u w]
    simp only [map_add (f := _), map_smul]
    module
  have e1 := hQ.apply_vec (fderiv ℝ (fun u => ρ u f) 0).toLinearMap w
  have e1' : (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = dH ρ (X w) f := e1
  have e2 := hQ (Complex.ofRealCLM.toLinearMap ∘ₗ (om.flip w).toLinearMap) w
  have e2' : 2 * π * I * ∑ i, c i * ((om (q i) w : ℂ) * (om (p i) w : ℂ) + (om (p i) w : ℂ) * (om (q i) w : ℂ))
      = (om (X w) w : ℂ) := e2
  have e3 : ∑ i, c i * ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om (q i) w : ℂ) * (om (p i) w : ℂ))))
      = π * I * (om (X w) w : ℂ) := by
    rw [← e2', Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i, c i • (2 * π * I : ℂ) • ρ w ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = ρ w (dH ρ (X w) f) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1', map_smul, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_comm]
  have e5 : quad ρ c p q (ρ w f) = ρ w (quad ρ c p q f) + ρ w (dH ρ (X w) f)
      + (π * I * (om (X w) w : ℂ)) • ρ w f := by
    rw [← e3, ← e4, Finset.sum_smul]
    unfold quad
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key, smul_add, smul_add, map_smul, smul_smul (c i) _ (ρ w f)]
  rw [h3, e5, skew]
  push_cast
  module

end GlobalTheory.Mem.Lift

end
