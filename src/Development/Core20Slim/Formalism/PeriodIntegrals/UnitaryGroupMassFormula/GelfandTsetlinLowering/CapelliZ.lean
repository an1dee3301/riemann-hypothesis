module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliShift
public import Development.Core20Slim.Lemmata.GeneralBFactRight.Imports
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTDefs
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.RealPlaceAnalysis.StatementE
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def CapScalar : Prop :=
  ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ s ∈ nablaSq ℂ n mu, ∀ u : ℂ,
      Formalism.REAL.qdet (capE h lam) u (φ s) = (∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ))) • φ s

def capF {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (i : Fin n) (v : ℤ) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((-1 : ℂ) ^ n) • Formalism.REAL.qdet (capE h lam) (-((v : ℂ) - ((i.1 : ℤ) : ℂ)))

def capZ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((List.finRange n).map fun i =>
    ((((Rset h lam sg i).erase (sg.w i)).toList.map fun v => capF h lam i v).prod)).prod

theorem list_scalar {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : List ι) (F : ι → Module.End ℂ V)
    (c : ι → ℂ) (x : V) (hL : ∀ j ∈ L, F j x = c j • x) : (L.map F).prod x = (L.map c).prod • x := by
  first | exact Bl.general_b_fact_right.goal1 .. | (apply Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> first | assumption | infer_instance)

theorem capF_scalar (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) (i : Fin n) (v : ℤ) :
    capF h lam i v (φ s) = (∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) • φ s := by
  rw [capF, LinearMap.smul_apply, hC h lam mu φ hφ s hs, smul_smul]
  congr 1
  have : ((-1 : ℂ) ^ n) = ∏ _j : Fin n, (-1 : ℂ) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring

theorem capZ_scalar (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    capZ h lam sg (φ s) = ((zScalar h lam sg mu : ℤ) : ℂ) • φ s := by
  unfold capZ
  rw [list_scalar (List.finRange n) _
    (fun i => ∏ v ∈ (Rset h lam sg i).erase (sg.w i),
      ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s)]
  · rw [← Fin.prod_univ_def]
    unfold zScalar
    push_cast
    rfl
  · intro i _
    rw [list_scalar _ _ (fun v => ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s),
      Finset.prod_map_toList]
    intro v _
    exact capF_scalar hC h lam mu φ hφ s hs i v

def presRing {N : ℕ} (lam : DomWeight N) : Subring (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) where
  carrier := {Q | ∀ f ∈ nablaSq ℤ N lam, ∃ f' ∈ nablaSq ℤ N lam,
    Q (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) f'}
  mul_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    obtain ⟨f3, hf3, e3⟩ := h1 f2 hf2
    exact ⟨f3, hf3, by rw [Module.End.mul_apply, e2, e3]⟩
  one_mem' := fun f hf => ⟨f, hf, rfl⟩
  add_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    exact ⟨f1 + f2, add_mem hf1 hf2, by rw [LinearMap.add_apply, e1, e2, map_add (f := _)]⟩
  zero_mem' := fun f hf => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro Q h1 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    exact ⟨-f1, neg_mem hf1, by rw [LinearMap.neg_apply, e1, map_neg]⟩

theorem algebraMap_int_mem {N : ℕ} (lam : DomWeight N) (w : ℤ) :
    algebraMap ℂ (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) (w : ℂ) ∈ presRing lam := by
  rw [map_intCast]; exact intCast_mem _ w

theorem pol_mem_presRing {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    (pol ℂ (m := N) a b : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) ∈ presRing lam := by
  intro f hf
  exact ⟨pol ℤ a b f, pol_mem_dualWeyl ℤ lam.natW a b f hf, pol_map _ a b f⟩

theorem capE_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) : capE h lam a b ∈ presRing lam := by
  unfold capE
  refine add_mem (pol_mem_presRing lam _ _) ?_
  split_ifs
  · exact algebraMap_int_mem lam _
  · exact zero_mem _

theorem qdet_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (w : ℤ) :
    Formalism.REAL.qdet (capE h lam) (w : ℂ) ∈ presRing lam := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.list_prod_mem _ fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Formalism.REAL.Tm
  refine add_mem ?_ (capE_mem h lam _ _)
  split_ifs
  · have : (w : ℂ) - (k : ℂ) = ((w - (k.1 : ℤ) : ℤ) : ℂ) := by push_cast; rfl
    rw [this]; exact algebraMap_int_mem lam _
  · exact zero_mem _

theorem capF_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (i : Fin n) (v : ℤ) :
    capF h lam i v ∈ presRing lam := by
  unfold capF
  have h1 : (-((v : ℂ) - ((i.1 : ℤ) : ℂ))) = ((-(v - (i.1 : ℤ)) : ℤ) : ℂ) := by push_cast; ring
  have h2 : ((-1 : ℂ) ^ n) = (((-1 : ℤ) ^ n : ℤ) : ℂ) := by push_cast; ring
  rw [h1, h2, Algebra.smul_def]
  exact mul_mem (algebraMap_int_mem lam _) (qdet_mem h lam _)

theorem capZ_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    capZ h lam sg ∈ presRing lam := by
  unfold capZ
  refine Subring.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  refine Subring.list_prod_mem _ fun y hy => ?_
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
  exact capF_mem h lam i v

theorem capelliZ_of (hC : CapScalar) : CapelliZ := by
  intro n N h lam sg _
  refine ⟨capZ h lam sg, fun f hf => capZ_mem h lam sg f hf, ?_⟩
  intro mu _ φ hφ s hs
  exact capZ_scalar hC h lam sg mu φ hφ s hs

end PI.WGL
