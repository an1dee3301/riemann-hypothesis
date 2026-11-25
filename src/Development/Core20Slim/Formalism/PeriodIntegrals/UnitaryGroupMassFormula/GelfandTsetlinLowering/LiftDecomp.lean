module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTDefs
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem dominant_weight_ext {N : ℕ} (a b : DomWeight N) (hab : a.w = b.w) : a = b := by
  obtain ⟨w, hw⟩ := a
  obtain ⟨w', hw'⟩ := b
  simp only at hab
  subst hab
  rfl

theorem extremal_mem_nablaSq' (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (fun i j hij => Int.toNat_le_toNat (by have := mu.anti hij; omega))

theorem degree_sub_det_shift_nonneg {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu) : 0 ≤ degZ lam mu - lam.detShift := by
  subst h
  have hle : ∀ i : Fin n, mu.w i ≤ lam.w (Fin.castSucc i) := fun i => (hmu i).1
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)
  have hl : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left (by omega)]
    congr 1
  unfold degZ wsum
  rw [hl, Fin.sum_univ_castSucc]
  linarith

theorem weight_sum_eq_of_last_gap {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu sg : DomWeight n)
    (hmu : Interlace h lam mu) (hsg : Interlace h lam sg) (hd : dLast lam mu = dLast lam sg) :
    wsum mu = wsum sg := by
  have h1 := degree_sub_det_shift_nonneg h lam mu hmu
  have h2 := degree_sub_det_shift_nonneg h lam sg hsg
  unfold dLast at hd
  have h3 : degZ lam mu - lam.detShift = degZ lam sg - lam.detShift := by
    rw [← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hd]
  unfold degZ at h3
  linarith

theorem decomp_of (h4 : PI.GTBranch) (hL : EqvLast) : Decomp := by
  intro n N h lam sg hsg io0 hio hne f hf hfw
  classical
  let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nablaSq ℂ n sg).map io0 ⊔ OtherPart h lam sg
  have key : nablaSq ℂ N lam ≤ T.comap (weightedHomogeneousComponent (lastW N) (dLast lam sg)) := by
    rw [(h4 n N h lam).2]
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro s hs
    rw [Submodule.mem_comap, Submodule.mem_comap]
    have hφ' : IsEqv h mu lam φ := hφ
    have hhom := hL n N h lam mu hmu φ hφ' s hs
    by_cases hd : dLast lam mu = dLast lam sg
    · rw [hd] at hhom
      rw [hhom.weightedHomogeneousComponent_same]
      have hw : wsum mu = wsum sg := weight_sum_eq_of_last_gap h lam mu sg hmu hsg hd
      by_cases hmw : mu.w = sg.w
      · have hms : mu = sg := dominant_weight_ext mu sg hmw
        subst hms
        have hboth : ∀ ψ ∈ ({φ, io0} : Set (MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)),
            (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
            ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
              ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s) := by
          intro ψ hψ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
          rcases hψ with rfl | rfl
          · exact hφ'
          · exact hio
        obtain ⟨_, c, hc⟩ := (h4 n N h lam).1 mu φ io0 hboth ⟨extremal ℂ n mu, extremal_mem_nablaSq' n mu, hne⟩
        refine Submodule.mem_sup_left ?_
        rw [hc s hs, ← map_smul]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ c hs)
      · refine Submodule.mem_sup_right ?_
        unfold OtherPart
        exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (Submodule.mem_iSup_of_mem hmw
          (Submodule.mem_iSup_of_mem hw (Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ'
            (Submodule.mem_map_of_mem hs))))))
    · rw [hhom.weightedHomogeneousComponent_ne (dLast lam sg) (Ne.symm hd)]
      exact zero_mem _
  have hfT := key hf
  rw [Submodule.mem_comap, hfw.weightedHomogeneousComponent_same] at hfT
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hfT
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
  refine ⟨u, hu, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

end PI.WGL
