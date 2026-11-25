module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipRadicalOfRational
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipRadicalOfRational.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipRadicalOfRational.Statement h v := by
  classical
  intro x₀ γ hx hz
  have hγ : ∀ u : W, γ • u = (γ : W ≃ₗ[E] W) u := fun _ => rfl

  have key : ∃ y : W, ∀ u : W, ∃ a : E,
      γ • u = u + h.toSesq x₀ u • (γ • y - y) + a • x₀ := by
    by_cases hy : ∃ y, h.toSesq x₀ y = 1
    · obtain ⟨y, hy⟩ := hy
      refine ⟨y, fun u => ?_⟩
      obtain ⟨a, ha⟩ := hz (u - h.toSesq x₀ u • y)
        (by rw [map_sub, map_smul, smul_eq_mul, hy, mul_one, sub_self])
      have hs : γ • (u - h.toSesq x₀ u • y) = γ • u - h.toSesq x₀ u • (γ • y) := by
        simp only [hγ, map_sub, map_smul]
      rw [hs] at ha
      refine ⟨a, ?_⟩
      rw [smul_sub, sub_eq_iff_eq_add.mp ha]
      abel
    · refine ⟨0, fun u => ?_⟩
      have h0 : h.toSesq x₀ u = 0 := by
        by_contra hu
        exact hy ⟨(h.toSesq x₀ u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
      obtain ⟨a, ha⟩ := hz u h0
      exact ⟨a, by simp [ha]⟩
  obtain ⟨y, hy⟩ := key
  choose a ha using fun j => hy (v j)
  rw [mem_unipRadical]
  intro w
  set M : Matrix ι ι ℂ := (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
    Matrix ι ι ℂ) with hM
  have hvec : ∀ x : W, M *ᵥ vecAt v x w = vecAt v (γ • x) w := fun x =>
    congrFun (archEmbed_smul_vecAt h v γ x) w

  have hcol : ∀ i j, M i j = w.embedding (v.repr (γ • v j) i) := by
    intro i j
    have := congrFun (hvec (v j)) i
    simpa [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite,
      eq_comm] using this
  refine ⟨by rw [hvec, hx], fun z hz0 => ?_⟩

  have hℓ : ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j = 0 := by
    rw [← hz0]
    have hH : ∀ j, w.embedding (h.toSesq x₀ (v j)) =
        ∑ i, star (vecAt v x₀ w i) * gramAt h v w i j := by
      intro j
      rw [HermAtPlace.proof h v w x₀ (v j)]
      simp [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite]
    simp only [hH, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∑ j, w.embedding (a j) * z j, ?_⟩
  funext i
  have hrow : (M *ᵥ z) i = ∑ j, (w.embedding (if i = j then 1 else 0) +
      w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) +
      w.embedding (a j) * w.embedding (v.repr x₀ i)) * z j := by
    simp only [mulVec, dotProduct, hcol]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]
    simp [Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  have e1 : ∑ j, w.embedding (if i = j then 1 else 0) * z j = z i := by
    simp [apply_ite]
  have e2 : ∑ j, w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) * z j =
      w.embedding (v.repr (γ • y - y) i) * ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, w.embedding (a j) * w.embedding (v.repr x₀ i) * z j =
      (∑ j, w.embedding (a j) * z j) * w.embedding (v.repr x₀ i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, hℓ]
  simp [vecAt]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
