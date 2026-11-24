module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegralAdeleMulVecMemLatticeClosureStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorLatticeMulTransposeStableIffStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
open scoped Classical

noncomputable section
namespace GlobalTheory.IdemCut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem smul_phi_of_mul_eq_zero {a e : AF F} (h : a * e = 0) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_zero, zero_smul, add_zero]

theorem smul_phi_of_mul_eq_self {a e : AF F} (h : a * e = a) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • M := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_self, zero_smul, zero_add]

theorem idempotentCut_latticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₁ ⊆ S →
      (∀ w ∉ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u * e = 0 ∨ u * e = u) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  intro F E _ _ _ _ _ σ B a a' G hG h
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h) G.W.L hG.hW.lat
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h⁻¹) G.W.L hG.hW.lat
  refine ⟨S₁ ∪ S₂, fun S e he hS hcut => ?_⟩
  have key : ∀ w ∉ S, ∀ (X : ℕ) (Xs : Spc F E X), ∀ γ,
      γ * (mat (loc e he h))ᵀ ∈ latAtV Xs G.W w ↔ γ ∈ latAtV Xs G.W w := by
    intro w hw X Xs γ
    have hw1 : w ∉ S₁ := fun h' => hw (hS (Finset.mem_union_left _ h'))
    have hw2 : w ∉ S₂ := fun h' => hw (hS (Finset.mem_union_right _ h'))
    refine GlobalTheory.T.tensorLattice_mul_transpose_stable_iff F E X _ Xs G.W w _ _ (mat_inv_mul (loc e he h)) ?_ ?_ γ
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₁ w hw1 u hu hint y hy
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc_inv]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₂ w hw2 u hu hint y hy
  exact ⟨fun w hw => key w hw _ G.V, fun w hw => key w hw _ G.V'⟩

end GlobalTheory.IdemCut
end
