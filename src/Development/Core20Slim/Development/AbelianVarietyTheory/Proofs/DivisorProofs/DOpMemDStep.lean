module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
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
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.FockKFin

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) : Submodule ℂ (SInf F κ) :=
  Submodule.span ℂ {h | ∃ a b : κ → mixedEmbedding.mixedSpace F, ∃ f ∈ P, h = dOp a b f}

theorem dOp_mem_dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) (a b : κ → mixedEmbedding.mixedSpace F)
    {f : SInf F κ} (hf : f ∈ P) : dOp a b f ∈ dStep P :=
  Submodule.subset_span ⟨a, b, f, hf, rfl⟩

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {g | GaussD M τ g}

def polLe (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (vacSp M τ) (fun _ P => P ⊔ dStep P) m

theorem polLe_zero (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : polLe M τ 0 = vacSp M τ := rfl

theorem polLe_succ (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    polLe M τ (m + 1) = polLe M τ m ⊔ dStep (polLe M τ m) := rfl

theorem polLe_mono (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Monotone (polLe M τ) :=
  monotone_nat_of_le_succ fun m => by rw [polLe_succ]; exact le_sup_left

def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.FockKFin

end
