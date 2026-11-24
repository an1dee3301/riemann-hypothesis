module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem fourier_prod_symm_preserving :
    ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  intro A _ _ ν _ ψ ι _ _ Bm hsym hemb hmap t f hf hint hinv
  have hψ : ∀ (s : Finset ι) (h : ι → A), ψ (∑ i ∈ s, h i) = ∏ i ∈ s, ψ (h i) := by
    intro s h
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  have hsplit : ∀ (g : A → ℂ) (x w : ι → A),
      (∏ i, g (x i)) * ψ (dotProduct x w) = ∏ i, (g (x i) * ψ (x i * w i)) := by
    intro g x w
    rw [Finset.prod_mul_distrib]
    congr 1
    exact hψ Finset.univ _
  have key : ∀ w : ι → A, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x w)
      ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (w i) := by
    intro w
    simp_rw [hsplit t]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => t x * ψ (x * w i))]
    exact Finset.prod_congr rfl fun i _ => (hf (w i)).symm
  refine ⟨fun y => key _, ?_, ?_⟩
  · have h1 : Integrable (fun w : ι → A => ∏ i, f (w i)) (Measure.pi fun _ : ι => ν) :=
      Integrable.fintype_prod (fun _ => hint)
    rw [← hmap] at h1
    exact (hemb.integrable_map_iff).1 h1
  · intro z
    have hdot : ∀ y : ι → A, dotProduct y (Bm.mulVec z) = dotProduct (Bm.mulVec y) z := by
      intro y
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose Bm y, ← hsym.eq]
      simp [hsym.eq]
    have hG : ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z))
          ∂(Measure.pi fun _ : ι => ν)
        = ∫ w : ι → A, (∏ i, f (w i)) * ψ (dotProduct w z)
          ∂((Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x)) := by
      rw [hemb.integral_map]
      simp_rw [hdot]
    rw [hG, hmap]
    simp_rw [hsplit f]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i x => f x * ψ (x * z i))]
    exact Finset.prod_congr rfl fun i _ => hinv (z i)

end GlobalTheory.CompanionTheory.BigCell
