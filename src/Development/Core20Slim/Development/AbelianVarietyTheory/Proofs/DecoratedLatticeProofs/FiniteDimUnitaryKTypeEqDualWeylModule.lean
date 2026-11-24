module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCTypeWConj
public import Batteries.Classes.RatCast
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms
open scoped InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.DualWeylType

open GlobalTheory.ConjugateType

theorem dual_weyl_type : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (lamH : Fin k → ℝ), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ (Formalism.QuantumDeterminants.lowK (allPos k) lamH) ⊤ → (∀ i : Fin k, -lamH (Fin.rev i) = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∃ (j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ H), (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ a a', normFock lam (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (σ (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  intro k n h lam H _ _ _ σ lamH hσ hK hrho

  obtain ⟨hσ', hK'⟩ := GlobalTheory.ConjTwist.conj_twist_isKTypeOf k _ 0 H σ hσ hK

  obtain ⟨E, iE1, iE2, iE3, π, J, hJ, hπ, hπK, hπJ⟩ := exists_conjugate_type k _ H _ hσ' hK'
  have hJσ : ∀ g u, π g (J u) = J (σ g u) := by
    intro g u
    rw [hπJ]
    simp only [zpow_zero, one_smul, map_star_star]

  have hlow : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -lamH (Fin.rev i)) =
      fun a => ((0 : ℤ) : ℝ) - Formalism.QuantumDeterminants.lowK (allPos k) lamH (Fin.rev a) := by
    rw [GlobalTheory.ConjTypeW.lowK_neg_rev]
    funext a
    simp
  have hnt : Nontrivial E := by
    obtain ⟨-, -, -, ⟨v, -, hv0, -⟩, -⟩ := hπK
    exact ⟨⟨v, 0, hv0⟩⟩
  have hHC : IsHCTypeU k (fun i => -lamH (Fin.rev i)) π := ⟨hnt, iE3, hπ, by rw [hlow]; exact hπK⟩

  obtain ⟨jE, hmem, hsurj, hfock, heq⟩ :=
    GlobalTheory.WeylConjType.exists_conj_weyl k n h lam _ hrho E π hHC

  let j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    { toFun := fun ξ => jE (J ξ)
      map_add' := fun x y => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c x => by
        rw [map_smulₛₗ, map_smulₛₗ, RingHom.id_apply, Complex.conj_conj] }
  have hj : ∀ ξ, j ξ = jE (J ξ) := fun _ => rfl

  let Φ : H →ₗ[ℂ] ConjSp E :=
    { toFun := fun ξ => ConjSp.mk (J ξ)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by
        show ConjSp.mk (J (c • x)) = c • ConjSp.mk (J x)
        have e := (ConjSp.mkL E).map_smulₛₗ (starRingEnd ℂ c) (J x)
        rw [Complex.conj_conj] at e
        rw [map_smulₛₗ]
        exact e }
  have hΦ : Function.Bijective Φ := hJ
  let Ψ : H ≃ₗ[ℂ] ConjSp E := LinearEquiv.ofBijective Φ hΦ
  let f := stdOrthonormalBasis ℂ (ConjSp E)
  refine ⟨j, _, f.toBasis.map Ψ.symm, fun ξ => hmem _, fun p hp => ?_, fun a a' => ?_, fun g hg ξ => ?_⟩
  · obtain ⟨η, rfl⟩ := hsurj p hp
    obtain ⟨ξ, rfl⟩ := hJ.2 η
    exact ⟨ξ, rfl⟩
  · have hb : ∀ a, J ((f.toBasis.map Ψ.symm) a) = ConjSp.out (f a) := by
      intro a
      rw [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
      have := Ψ.apply_symm_apply (f a)
      exact this
    rw [hj, hj, hfock, hb, hb]
    show ⟪f a', f a⟫_ℂ = _
    rw [orthonormal_iff_ite.1 f.orthonormal]
    rcases eq_or_ne a a' with rfl | hA
    · simp
    · rw [if_neg hA.symm, if_neg hA]
  · rw [hj, hj, ← hJσ, heq g hg]

end GlobalTheory.DualWeylType
