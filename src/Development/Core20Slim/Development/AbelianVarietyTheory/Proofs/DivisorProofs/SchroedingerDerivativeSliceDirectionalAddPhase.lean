module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Prod
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchDeriv
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem archimedean_map_add (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (a + b) = GlobalTheory.WeilL2Words.arch1 F a + GlobalTheory.WeilL2Words.arch1 F b := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact map_add _ a b
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem adeleOfMixedSpaceComponent_finsetSum (f : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (∑ k, f k) = ∑ k, GlobalTheory.WeilL2Words.arch1 F (f k) :=
  map_sum (AddMonoidHom.mk' (GlobalTheory.WeilL2Words.arch1 F) (archimedean_map_add F)) f Finset.univ

theorem adeleJoin_mul_arch1 (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) (k : κ)
    (b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilCont.adeleJoin F x y k * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (x k * b) := by
  unfold GlobalTheory.WeilL2Words.arch1 GlobalTheory.WeilCont.adeleJoin
  refine Prod.ext ?_ ?_
  · exact (map_mul _ (x k) b).symm
  · exact mul_zero (y k)

theorem adeleOfMixedSpaceComponent_mul (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F a * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (a * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact (map_mul _ a b).symm
  · exact mul_zero (0 : FiniteAdeleRing (𝓞 F) F)

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + GlobalTheory.WeilL2Words.arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (map_add _ (x i) (v i)).symm
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x w : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, x k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleJoin_mul_arch1 F x y k (w k)

theorem arch_dot_arch (v w : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch F v ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, v k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleOfMixedSpaceComponent_mul F (v k) (w k)

theorem mul_arch1 [Invertible (2 : AdeleRing (𝓞 F) F)] (b : mixedEmbedding.mixedSpace F) :
    ⅟(2 : AdeleRing (𝓞 F) F) * GlobalTheory.WeilL2Words.arch1 F b =
      GlobalTheory.WeilL2Words.arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · show (⅟(2 : AdeleRing (𝓞 F) F)).1 * _ = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero _

end GlobalTheory.ArchDeriv

open GlobalTheory.ArchDeriv
namespace GlobalTheory.WeilL2Words

theorem dS_adeleJoin_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hs h x
  set s : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y) with hs_def
  set P : mixedEmbedding.mixedSpace F := ∑ k, x k * h.2 k with hP
  set Q : mixedEmbedding.mixedSpace F :=
    InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, h.1 k * h.2 k with hQ
  set r : ℝ → ℝ := fun t => t * ℓ P + t ^ 2 * ℓ Q with hr
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)) * s (x + t • h.1) := by
    funext t
    have e1 : (t • h).1 = t • h.1 := rfl
    have e2 : (t • h).2 = t • h.2 := rfl
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilL2Words.archPair, e1, e2, adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch,
      mul_arch1, ← archimedean_map_add]
    congr 1
    · rw [hψ]
      congr 2
      have q1 : (∑ k, x k * (t • h.2) k) = t • P := by
        simp only [hP, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
      have q2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 *
          ∑ k, (t • h.1) k * (t • h.2) k = t ^ 2 • Q := by
        simp only [Pi.smul_apply, smul_mul_smul_comm]
        rw [← Finset.smul_sum, mul_smul_comm, hQ, pow_two]
      rw [q1, q2, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hr' : HasDerivAt r (ℓ P) 0 := by
    have h1 := (hasDerivAt_mul_const (x := (0 : ℝ)) (ℓ P)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (ℓ Q))
    exact h1.congr_deriv (by simp)
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * (r 0 : ℂ)) * (2 * Real.pi * Complex.I * (ℓ P : ℂ))) 0 :=
    (hr'.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hc : HasDerivAt (fun t : ℝ => x + t • h.1) h.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add x
  have hS : HasDerivAt (fun t : ℝ => s (x + t • h.1)) (fderiv ℝ s x h.1) 0 := by
    have hf : HasFDerivAt s (fderiv ℝ s x) (x + (0 : ℝ) • h.1) := by
      rw [zero_smul, add_zero]
      exact (hs x).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hc
  have hD := hE.mul hS
  unfold GlobalTheory.WeilL2Words.dS
  rw [key]
  refine hD.deriv.trans ?_
  have r0 : r 0 = 0 := by simp [hr]
  simp only [r0, zero_smul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring

end GlobalTheory.WeilL2Words

end
