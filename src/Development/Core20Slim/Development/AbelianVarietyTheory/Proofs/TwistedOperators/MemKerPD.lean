module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kerPD (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) :
    Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :=
  Submodule.span ℂ {Φ₀D | Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
    ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0}

theorem mem_kerPD {ψ : AddChar (AF D.host.F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (θ : InfFam D) {W W₁ X : HSp D}
    (A₁ : Fr W₁) (B : Fr X) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) (Φ₀D : (Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :
    Φ₀D ∈ kerPD ψ θ A₁ B Bs Γ cB p' ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
      ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  have hl := isDatum_linear Γ.M' ψ hψ (⇑cB)
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, hl.1, map_zero p'⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    obtain ⟨hy1, Φy, hΦy, hDy, hpy⟩ := hy
    refine ⟨Submodule.add_mem _ hx1 hy1, Φx + Φy, Submodule.add_mem _ hΦx hΦy, ?_, by rw [map_add (f := _), hpx, hpy, add_zero]⟩
    have := hl.2 x y Φx Φy 1 hDx hDy
    simpa using this
  | smul c x _ hx =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    refine ⟨Submodule.smul_mem _ c hx1, c • Φx, Submodule.smul_mem _ c hΦx, ?_, by rw [map_smul, hpx, smul_zero]⟩
    have := hl.2 0 x 0 Φx c hl.1 hDx
    simpa using this

end GlobalTheory.SquareAgree

end
