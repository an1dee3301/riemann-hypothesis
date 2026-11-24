module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (n : ℕ) :
    HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n) where
  toFun b w := ⟨matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w, by
    refine mem_hermC.2 ?_
    ext a c
    simp only [Matrix.conjTranspose_apply, matC, RCLike.star_def]
    rw [← hconj, b.2 a c]⟩
  invFun G := ⟨fun a c => Θ.symm fun w => (G w : Matrix (Fin n) (Fin n) ℂ) a c, by
    intro a c
    apply Θ.injective
    funext w
    have h : (G w : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 (G w).2
    rw [hconj]
    simp only [RingEquiv.apply_symm_apply]
    have := congrFun (congrFun h a) c
    simpa [Matrix.conjTranspose_apply] using this⟩
  left_inv b := by
    apply Subtype.ext
    ext a c
    simp [matC]
  right_inv G := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]
  map_add' b b' := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]

theorem continuous_hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n) := by
  refine continuous_pi fun w => Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  have h1 : Continuous fun b : HermR (Ainf F) σ n =>
      (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact (continuous_apply w).comp (hΘ.comp h1)

theorem continuous_hermEquiv_symm (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ.symm) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n).symm := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  refine hΘ.comp (continuous_pi fun w => ?_)
  have h1 : Continuous fun b : hermC n => (b : Matrix (Fin n) (Fin n) ℂ) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact h1.comp (continuous_apply w)

theorem continuous_symm (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    Continuous Θ.symm := by
  have e : (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) = (hΘ.homeomorph Θ).symm := by
    funext y
    apply (hΘ.homeomorph Θ).injective
    rw [Homeomorph.apply_symm_apply]
    exact Θ.apply_symm_apply y
  rw [e]
  exact (hΘ.homeomorph Θ).symm.continuous

theorem topAddGroup_tens (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    IsTopologicalAddGroup (Ainf F ⊗[F] E) := by
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  refine { continuous_add := ?_, continuous_neg := ?_ }
  · have : (fun p : (Ainf F ⊗[F] E) × (Ainf F ⊗[F] E) => p.1 + p.2) =
        fun p => Θ.symm (Θ p.1 + Θ p.2) := by
      funext p; simp
    rw [this]
    exact c2.comp ((c1.comp continuous_fst).add (c1.comp continuous_snd))
  · have : (fun x : Ainf F ⊗[F] E => -x) = fun x => Θ.symm (-Θ x) := by
      funext x; simp
    rw [this]
    exact c2.comp c1.neg

theorem exists_hermEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  intro F E _ _ _ _ _ σ _ e τ Θ hc n
  obtain ⟨hΘ, hconj, -, -⟩ := hc
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  haveI := topAddGroup_tens Θ hΘ
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  have h1 := continuous_hermEquiv σ Θ hconj c1 n
  have h2 := continuous_hermEquiv_symm σ Θ hconj c2 n
  refine ⟨hermEquiv σ Θ hconj n, fun b w => rfl, fun ν hν => ⟨?_, fun G hG => ?_⟩⟩
  · exact AddEquiv.isAddHaarMeasure_map ν (hermEquiv σ Θ hconj n) h1 h2
  · exact hG.comp_measurable h1.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord
