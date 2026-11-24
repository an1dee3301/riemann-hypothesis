module

public import Mathlib
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

@[expose] public section

noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp [Measure.pi_of_empty]
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove μ 0
    have hg : Measurable fun y : (j : Fin n) → E (Fin.succAbove 0 j) =>
        ∏ j, f (Fin.succAbove 0 j) (y j) :=
      Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : (i : Fin (n + 1)) → E i,
            (fun z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)) =>
              f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j))
            (MeasurableEquiv.piFinSuccAbove E 0 x) ∂(Measure.pi μ) := by
          congr 1
          funext x
          rw [Fin.prod_univ_succ]
          (try simp only [Fin.succAbove_zero]) <;> rfl
      _ = ∫⁻ z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)),
            f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j)
            ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
          hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
            (fun z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)) =>
              f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j))
      _ = (∫⁻ a, f 0 a ∂μ 0) *
            ∫⁻ y, ∏ j, f (Fin.succAbove 0 j) (y j) ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
          lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
          rw [ih (fun j => f (Fin.succAbove 0 j)) (fun j => hf _), Fin.prod_univ_succ]
          simp [Fin.succAbove_zero]

theorem lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  have h1 : ∀ y : (i' : Fin (Fintype.card ι)) → E (e i'),
      ∏ i, f i ((MeasurableEquiv.piCongrLeft E e) y i) = ∏ i', f (e i') (y i') := by
    intro y
    exact (Fintype.prod_equiv e (fun i' => f (e i') (y i')) _
      (fun i' => by simp [MeasurableEquiv.piCongrLeft_apply_apply])).symm
  simp_rw [h1]
  rw [lintegral_fin_prod (fun i' => f (e i')) (fun i' => hf (e i'))]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)



end PI.AprimeInfG
