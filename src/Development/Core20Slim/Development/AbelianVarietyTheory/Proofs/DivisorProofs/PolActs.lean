module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealActs

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def DerOn (N : Submodule ℂ (SInf F κ)) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, ActsD (evI F) T f f₁ ↔ f₁ = D f

def OpOn (N : Submodule ℂ (SInf F κ)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, Acts (evI F) T f f₁ ↔ f₁ = D f

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def PolActs (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) : Prop :=
  (∀ γ ∈ Lines σ X, DerOn (M.Pol B.ψ B.emb) (fun t => om (γ (Multiplicative.ofAdd t), 1))) ∧
  (∀ k ∈ KInf σ X B.emb, OpOn (M.Pol B.ψ B.emb) (om (k, 1))) ∧
  (∀ γ ∈ Lines σ W, DerOn (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t)))) ∧
  ∀ k ∈ KInf σ W B.emb, OpOn (M.Pol B.ψ B.emb) (om (1, k))

def KerStab (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f = 0 → p f₁ = 0) ∧
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (om (1, k)) f f₁ → p f = 0 → p f₁ = 0

def Irred (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  ∀ N : Submodule ℂ P,
    (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N) → N = ⊥ ∨ N = ⊤

end GlobalTheory.RealActs

end
