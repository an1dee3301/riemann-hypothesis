module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
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
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Push

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.FockVac

theorem span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  by_cases h : ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧ g ≠ 0
  · obtain ⟨g, hg, hg0⟩ := h
    have hle : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} ≤ Submodule.span ℂ {g} := by
      refine Submodule.span_le.2 fun f hf => ?_
      obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M B.ψ B.emb hP.base.cm hP.base.std
        (fun w => (hP.herm.cartan w).1) (fun w => (hP.skew.cartan w).1) f g hg hg0 hf
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    exact Submodule.finiteDimensional_of_le hle
  · push_neg at h
    have hb : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} = ⊥ :=
      Submodule.span_eq_bot.2 fun f hf => by_contra fun h0 => h0 (h f hf)
    rw [hb]
    infer_instance

end GlobalTheory.FockVac
