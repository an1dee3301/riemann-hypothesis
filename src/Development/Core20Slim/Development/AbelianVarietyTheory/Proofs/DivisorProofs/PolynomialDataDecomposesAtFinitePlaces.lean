module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImgSet
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
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
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem smul_pure {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    c • pure f φ = pure (c • f) φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_decOn_some {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ PolData B M) :
    ∃ (T₀ : Finset (Pl (F := F))) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ), DecOn B M T₀ Φ m f φ := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hcof, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hcof
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hv => ?_⟩, ?_⟩
    · by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    · simp
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    obtain ⟨T', m', f', φ', h1', rfl⟩ := hy
    refine ⟨T ∪ T', m + m', Fin.append f f', Fin.append φ φ', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    refine ⟨T, m, fun j => c • f j, φ, fun j => ⟨Submodule.smul_mem _ c (h1 j).1, (h1 j).2.1, (h1 j).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_pure c (f j) (φ j)

end GlobalTheory.ThK.CycGen

end
