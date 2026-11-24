module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.StatementA
public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.RealPlaceAnalysis.StatementU
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId 
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusComp

def ht {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * μ i

theorem ht_add {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ + ν) = ht μ + ht ν := by
  simp [ht, mul_add, Finset.sum_add_distrib]

theorem ht_sub {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ - ν) = ht μ - ht ν := by
  simp [ht, mul_sub, Finset.sum_sub_distrib]

theorem ht_root {n : ℕ} (a b : Fin n) : ht (Formalism.REAL.root a b) = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [ht, Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem weight_shift {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {ν : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F ν x) {a b : Fin n} (hab : ε a = ε b) :
    Formalism.REAL.IsWeight F (ν + Formalism.REAL.root a b) (F a b x) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ W => T x) (hF c c a b rfl hab)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, add_smul, add_comm]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, add_smul, sub_smul, add_comm]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2]

theorem word_weight {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {μ : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F μ x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∃ ν, ht μ ≤ ht ν ∧ Formalism.REAL.IsWeight F ν (ew F w x) := by
  induction w with
  | nil => exact ⟨μ, le_rfl, by simpa [ew] using hx⟩
  | cons p w ih =>
    obtain ⟨ν, h1, h2⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p (List.mem_cons_self ..)
    refine ⟨ν + Formalism.REAL.root p.1 p.2, ?_, ?_⟩
    · rw [ht_add, ht_root]
      have : ((p.2 : ℕ) : ℝ) < ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp.2
      linarith
    · simpa only [ew, Module.End.mul_apply] using weight_shift hF h2 hp.1

theorem comp_weight {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℝ} {G : Arr V n 1}
    (hG : Formalism.REAL.IsWeight (arrE E 1) ν G) (a b : Fin n) :
    Formalism.REAL.IsWeight E (ν - Formalism.REAL.root a b) (G (fun _ => (a, b))) := by
  intro c
  have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hG c)
  simp only at h1
  rw [arr_operator_one_apply, PiLp.smul_apply, add_comm, ← eq_sub_iff_add_eq] at h1
  rw [h1]
  by_cases h1 : a = c <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, sub_smul]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, Ne.symm h1, add_smul, sub_smul]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2, Ne.symm h1]



end GlobalTheory.Jet.VminusComp
