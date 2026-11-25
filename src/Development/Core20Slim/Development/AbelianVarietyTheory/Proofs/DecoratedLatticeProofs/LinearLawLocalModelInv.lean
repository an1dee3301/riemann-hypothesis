module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section

namespace GlobalTheory.LocOm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_inv_of_unit (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem nabs_pos_of_unit (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact NNReal.coe_pos.mpr distribHaarChar_pos

theorem linearFormula_inv_cancel {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (μS μT : kˣ →* ℂˣ)
    (gk : GL Y' k) (hk : GL Y k) (Φ : Matrix Y Y' k → ℂ) :
    (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk
      ((((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk⁻¹) : ℂˣ) : ℂ) • om μS⁻¹ gk⁻¹ hk⁻¹ Φ) = Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  have hx : ((↑(hk⁻¹⁻¹) : Matrix Y Y k) * ((↑(hk⁻¹) : Matrix Y Y k) * x * (↑gk : Matrix Y' Y' k)) *
      (↑(gk⁻¹) : Matrix Y' Y' k)) = x := by
    simp only [inv_inv, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hx]
  simp only [map_inv, nabs_inv_of_unit, Units.val_inv_eq_inv_val, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
  have p1 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det gk)
  have p2 := nabs_pos_of_unit (Matrix.GeneralLinearGroup.det hk)
  rw [Real.inv_rpow p1.le, Real.inv_rpow p2.le]
  push_cast
  simp only [neg_div]
  have q1 : ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p1 _).ne'
  have q2 : ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-((Fintype.card Y' : ℝ) / 2)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos p2 _).ne'
  have u1 := (μS (Matrix.GeneralLinearGroup.det gk)).ne_zero
  have u2 := (μS (Matrix.GeneralLinearGroup.det hk)).ne_zero
  have u3 := (μT (Matrix.GeneralLinearGroup.det gk)).ne_zero
  field_simp

theorem lawLoc_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k),
    LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g⁻¹ gk⁻¹ h⁻¹ hk⁻¹ := by
  intro D k _ _ _ _ S T ω μS μT Y Y' _ _ _ _ Tm g gk h hk hL Φ Φ' hΦ'
  have e : ω (g, h) (Tm Φ') = Tm Φ := hL Φ' Φ (by rw [hΦ', linearFormula_inv_cancel])
  rw [← e, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel]
  change ω 1 (Tm Φ') = Tm Φ'
  rw [map_one, Module.End.one_apply]

end GlobalTheory.LocOm

end
