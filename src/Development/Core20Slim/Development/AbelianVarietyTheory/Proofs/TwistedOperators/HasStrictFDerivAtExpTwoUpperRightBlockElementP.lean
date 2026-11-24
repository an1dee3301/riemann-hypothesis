module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

def twoPYLin (p q : ℕ) : (Fin p → Fin q → ℂ) →ₗ[ℝ] Mat p q where
  toFun C := pY C + pY C
  map_add' B C := by rw [pY_add]; abel
  map_smul' t B := by rw [pY_smul, smul_add]; rfl

def entryLin {p q : ℕ} (a b : Ix p q) : Mat p q →ₗ[ℝ] ℂ where
  toFun M := M a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Matrix.Norms.Operator in
theorem contDiff_exp_two_pY_entry (p q : ℕ) (a b : Ix p q) :
    ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => NormedSpace.exp (pY C + pY C) a b) := by
  have h1 : ContDiff ℝ 1 (NormedSpace.exp : Mat p q → Mat p q) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have h2 : ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => (pY C + pY C : Mat p q)) :=
    (LinearMap.toContinuousLinearMap (twoPYLin p q)).contDiff
  have h3 : ContDiff ℝ 1 (fun M : Mat p q => M a b) :=
    (LinearMap.toContinuousLinearMap (entryLin a b)).contDiff
  exact h3.comp (h1.comp h2)

theorem hasStrictFDerivAt_exp_two_pY : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  intro p q B h
  have hc : ContDiff ℝ 1 (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) =>
      NormedSpace.exp (pY C + pY C) a b) :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_exp_two_pY_entry p q a b
  have hs := hc.contDiffAt.hasStrictFDerivAt_fderiv (x := B) (by simp)
  refine ⟨_, hs, fun C => ?_⟩
  ext a b
  have hl : HasDerivAt (fun t : ℝ => B + t • C) C 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const C).const_add B
  have h1 := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 a) b
  have h3 := h (pY C + pY C) a b
  have e : (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • (pY C + pY C)) a b) =
      fun t : ℝ => NormedSpace.exp (pY (B + t • C) + pY (B + t • C)) a b := by
    funext t
    have e' : pY B + pY B + t • (pY C + pY C) = pY (B + t • C) + pY (B + t • C) := by
      rw [pY_add, pY_smul, smul_add]; abel
    rw [e']
  rw [e] at h3
  exact h2.unique h3

end GlobalTheory.PolarU
