module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
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
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.ContrHeis

variable {D : D7}

theorem symplOH_kappa {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w w' : WO S B'.L) : symplOH B.L S (l.κ S w) (l.κ S w') = -symplOH S B'.L w w' := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  obtain ⟨-, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)
  rw [symplOH, symplOH, hsym, Int.cast_one, one_mul, mul_neg]

theorem kappa_add {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w w' : WO S B'.L) : l.κ S (w + w') = l.κ S w + l.κ S w' := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).1 w w'

theorem kappa_rat {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w : WO S B'.L) (hw : w ∈ ratMx D B'.L.rank S.rank) : l.κ S w ∈ ratMx D S.rank B.L.rank := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.2.1 w hw

theorem contr_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (Ξ₁ : WO B.V₀ S → ℂ) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ x : WO S B'.L, GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂) = GlobalTheory.Unf.contr l S vL Ξ₁ Ξ₂ := by
  intro D ψ _ ρ σ B B' l S vL Ξ₁ Ξ₂ h₁ h₂ x
  funext u v
  have hT : ∀ (a b : WO S B'.A) (c d : WO S B'.L), symplOH S B'.V₀ ((B'.o.resT S).symm (a, c)) ((B'.o.resT S).symm (b, d)) =
      symplOH S B'.A a b + symplOH S B'.L c d := by
    intro a b c d
    rw [B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hS : ∀ (a b : WO B.A S) (c d : WO B.L S), symplOH B.V₀ S ((B.o.resS S).symm (a, c)) ((B.o.resS S).symm (b, d)) =
      symplOH B.A S a b + symplOH B.L S c d := by
    intro a b c d
    rw [B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  set G : WO S B'.L → ℂ := fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) with hG
  have step : ∀ w, heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂ ((B'.o.resT S).symm (v, w)) *
      heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) = G (w + x) := by
    intro w
    simp only [heisO, hG]
    rw [hT, hS, symplOH_zero_right, symplOH_zero_right, zero_add, zero_add, symplOH_kappa, ← map_add (f := _), ← map_add (f := _),
      Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero, ← kappa_add]
    have e : ψ (symplOH S B'.L w x) * ψ (-symplOH S B'.L w x) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (Ξ₂ ((B'.o.resT S).symm (v, w + x)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S (w + x)))) * e
  have per : ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ a, G (γ + a) = G a := by
    intro γ hγ a
    have r2 : (B'.o.resT S).symm (0, γ) ∈ ratMx D B'.V₀.rank S.rank := by
      refine (B'.o.mem_ratL_resT S _).2 ?_
      rw [AddEquiv.apply_symm_apply]
      exact ⟨zero_mem _, hγ⟩
    have r1 : (B.o.resS S).symm (0, l.κ S γ) ∈ ratMx D S.rank B.V₀.rank := by
      refine (B.o.mem_ratL_resS S _).2 ?_
      rw [AddEquiv.apply_symm_apply]
      exact ⟨zero_mem _, kappa_rat l S γ hγ⟩
    obtain ⟨γ₂, hγ₂⟩ := r2
    obtain ⟨γ₁, hγ₁⟩ := r1
    have q2 := h₂.quasi γ₂ ((B'.o.resT S).symm (v, a))
    have q1 := h₁.quasi γ₁ ((B.o.resS S).symm (u, l.κ S a))
    have e2 : ratW B'.V₀ S γ₂ = (B'.o.resT S).symm (0, γ) := hγ₂
    have e1 : ratW S B.V₀ γ₁ = (B.o.resS S).symm (0, l.κ S γ) := hγ₁
    rw [e2, ← map_add (f := _), Prod.mk_add_mk, zero_add, hT, symplOH_zero_left, zero_add] at q2
    rw [e1, ← map_add (f := _), Prod.mk_add_mk, zero_add, hS, symplOH_zero_left, zero_add, symplOH_kappa, neg_neg] at q1
    simp only [hG]
    rw [kappa_add, q2, q1]
    have e : ψ (-symplOH S B'.L γ a) * ψ (symplOH S B'.L γ a) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    linear_combination (Ξ₂ ((B'.o.resT S).symm (v, a)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S a))) * e
  simp only [contr]
  rw [show (fun w => heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂ ((B'.o.resT S).symm (v, w)) *
      heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) = fun w => G (w + x)
    from funext step]
  exact covolOne_integral_add vL.covol G per x

end GlobalTheory.Unf.ContrHeis

end
