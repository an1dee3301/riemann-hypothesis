module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
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
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.WeilChange

theorem weilData_differ_by_splitFac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → om' (g, h) f = ((splitFacO χS' χT' x y : ℂ) * (splitFacO χS χT x y : ℂ)⁻¹) • om (g, h) f := by
  intro D ψ S T χS χT χS' χT' om om' H H' g h x y hx hy f hf
  have rS : ResEta D (χS⁻¹ * χS') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resS) H'.resS) (by omega)
  have rT : ResEta D (χT⁻¹ * χT') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resT) H'.resT) (by omega)
  obtain ⟨om₂, H₂, h₂⟩ := exists_weilDatum_twist D ψ H.std S T χS χT (χS⁻¹ * χS') (χT⁻¹ * χT') om H
    (hecke_mul (hecke_inv H.hecS) H'.hecS) (hecke_mul (hecke_inv H.hecT) H'.hecT) rS rT
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at H₂
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ H.std S T χS' χT' om' om₂ H' H₂ (g, h) f hf, h₂ g h x y hx hy, LinearMap.smul_apply]
  congr 1
  rw [← Circle.coe_inv, ← Circle.coe_mul]
  congr 1
  simp only [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  generalize (χT' x)⁻¹ = a, (χS y)⁻¹ = b, χS' y = c, χT x = d
  apply Circle.ext
  simp only [Circle.coe_mul]
  ring

end GlobalTheory.WeilChange
