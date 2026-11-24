module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaRatInv

theorem invOf_two_eq' {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] :
    ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

theorem thetaSum_schr_rat_add {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (a b : κ → F)
    (w : (κ → AF F) × (κ → AF F)) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ ((fun i => algebraMap F (AF F) (a i), fun i => algebraMap F (AF F) (b i)) + w) Φ) =
      ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ (fun i => algebraMap F (AF F) (b i)) - (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ w.2)) *
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ) := by
  set ra : κ → AF F := fun i => algebraMap F (AF F) (a i) with hra
  set rb : κ → AF F := fun i => algebraMap F (AF F) (b i) with hrb
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : κ → F => ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ rb - ra ⬝ᵥ w.2)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  set rξ : κ → AF F := fun i => algebraMap F (AF F) (ξ i) with hrξ
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rξ + ra := by
    funext i; simp [hrξ, hra]
  have e3 : ∀ c d : κ → F, (fun i => algebraMap F (AF F) (c i)) ⬝ᵥ (fun i => algebraMap F (AF F) (d i)) =
      algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [dotProduct]
  rw [e1]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have hx : rξ + (ra + w.1) = rξ + ra + w.1 := (add_assoc _ _ _).symm
  rw [hx]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  conv_rhs => rw [← mul_one (ψ _), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq', ← e3, ← e3]
  simp only [add_dotProduct, dotProduct_add]
  have t : ∀ z : AF F, ⅟(2 : AF F) * z + ⅟(2 : AF F) * z = z := fun z => by
    rw [← add_mul, invOf_two_add_invOf_two, one_mul]
  linear_combination t (ra ⬝ᵥ w.2)

theorem norm_thetaSum_schr_ratPair_add : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ),
    ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (γ + w) Φ)‖ = ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).mp hγ
  rw [thetaSum_schr_rat_add ψ hψ.2.2.1 Φ a b w, norm_mul, hψ.2.1, one_mul]

end GlobalTheory.ThetaRatInv

end
