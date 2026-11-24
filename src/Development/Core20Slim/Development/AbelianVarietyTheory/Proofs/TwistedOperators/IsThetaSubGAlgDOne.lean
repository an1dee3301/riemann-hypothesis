module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
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
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SquareAgree

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

structure IsThetaSubG (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W)
    (N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop where

  le : N ≤ algD M ψ emb

  fin : ∀ (v : Pl (F := F)) (f : SInf F (Fin n × Fin d)) (φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ), f ∈ M.Pol ψ emb →
    (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) → φ v ∈ augAt om v → pure f φ ∈ N

  lie : ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb,
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ ∈ N

  cpt : ∀ k ∈ KInf σ X emb, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb, Acts (evI F) (om (k, 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ - pure f φ ∈ N

  stabFin : ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N

  stabLie : ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ algD M ψ emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

  stabCpt : ∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N

theorem IsDatum.fun_eq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (AE F E) → Z) (hc : Function.Surjective crd) {Φ : (Fin n × Fin d → AF F) → ℂ} {f f' : Z → ℂ}
    (h : IsDatum M ψ crd Φ f) (h' : IsDatum M ψ crd Φ f') : f = f' := by
  funext z
  obtain ⟨u, rfl⟩ := hc z
  rw [← h.2 u, ← h'.2 u]

end GlobalTheory.SquareAgree

end
