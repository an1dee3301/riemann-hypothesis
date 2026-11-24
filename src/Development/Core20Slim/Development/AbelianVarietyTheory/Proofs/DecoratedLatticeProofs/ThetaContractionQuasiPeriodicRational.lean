module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem contr_quasi : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → (∀ γ u v, contr l S vL f₁ f₂ (ratW S B.A γ + u) v = ψ (-(symplOH B.A S (ratW S B.A γ) u)) * contr l S vL f₁ f₂ u v) ∧ ∀ γ u v, contr l S vL f₁ f₂ u (ratW B'.A S γ + v) = ψ (-(symplOH S B'.A (ratW B'.A S γ) v)) * contr l S vL f₁ f₂ u v := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  constructor
  · intro γ u v
    have e0 : (B.o.resS S).symm (ratW S B.A γ, 0) = ratW S B.V₀ (γ * B.o.qA) := by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    simp only [contr]
    rw [← integral_const_mul]
    congr 1
    funext w
    have e : ((ratW S B.A γ + u, l.κ S w) : WO B.A S × WO B.L S) = (ratW S B.A γ, (0 : WO B.L S)) + (u, l.κ S w) := by simp
    rw [e, map_add (f := _), e0, h₁.quasi, ← e0, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, add_zero]
    ring
  · intro γ u v
    have e0 : (B'.o.resT S).symm (ratW B'.A S γ, 0) = ratW B'.V₀ S (B'.o.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    simp only [contr]
    rw [← integral_const_mul]
    congr 1
    funext w
    have e : ((ratW B'.A S γ + v, w) : WO S B'.A × WO S B'.L) = (ratW B'.A S γ, (0 : WO S B'.L)) + (v, w) := by simp
    rw [e, map_add (f := _), e0, h₂.quasi, ← e0, B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, add_zero]
    ring

end GlobalTheory.ContrComb
