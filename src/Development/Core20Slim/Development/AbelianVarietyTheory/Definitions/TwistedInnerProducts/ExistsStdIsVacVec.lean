module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



theorem hasInfExp_div {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η⁻¹) τ (a - b) := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  refine ⟨n - m, by push_cast; rw [hn, hm]; ring, h1, fun θ hθ x hx hτ => ?_⟩
  have e1 := h2 θ hθ x hx hτ
  have e2 := h3 θ hθ x hx hτ
  set z : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hz
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, e1, e2]
  by_cases h0 : z = 0
  · have a1 : n = 0 := by
      by_contra h; exact (χ x).coe_ne_zero (by rw [e1, h0, zero_zpow _ h])
    have a2 : m = 0 := by
      by_contra h; exact (η x).coe_ne_zero (by rw [e2, h0, zero_zpow _ h])
    simp [a1, a2]
  · rw [zpow_sub₀ h0, div_eq_mul_inv]


end GlobalTheory.Chain

end
