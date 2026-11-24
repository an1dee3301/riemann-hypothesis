module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Formalism.PeriodIntegrals.HwIrred
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Int.LemmasAux
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
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
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem natW_anti_D {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

theorem extremal_mem_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (natW_anti_D mu)

theorem extremal_ne_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW

def sqLinD (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := sqAct ℂ N lam g
  map_add' x y := by simp only [sqAct, map_add (f := _), smul_add]
  map_smul' c x := by
    simp only [sqAct, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem sqLinD_apply (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqLinD N lam g f = sqAct ℂ N lam g f := rfl

theorem isEqv_zero_D {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N) :
    IsEqv h mu lam 0 := by
  refine ⟨fun s _ => by
    simp only [LinearMap.zero_apply]
    exact Submodule.zero_mem _, fun g s _ => ?_⟩
  simp only [LinearMap.zero_apply]
  rw [← sqLinD_apply, map_zero]

theorem isEqv_smul_D {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) (c : ℂ) :
    IsEqv h mu lam (c • φ) := by
  refine ⟨fun s hs => ?_, fun g s hs => ?_⟩
  · rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ c (hφ.1 s hs)
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ.2 g s hs, ← sqLinD_apply, ← sqLinD_apply, map_smul]

theorem eq_on_of_extremal_D (hI : PI.HwIrred) (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N)
    {mu : DomWeight n} {lam : DomWeight N}
    {φ ψ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ}
    (hφ : IsEqv h mu lam φ) (hψ : IsEqv h mu lam ψ)
    (hext : φ (extremal ℂ n mu) = ψ (extremal ℂ n mu)) : ∀ s ∈ nablaSq ℂ n mu, φ s = ψ s := by
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := nablaSq ℂ n mu ⊓ LinearMap.ker (φ - ψ)
  have hU : U ≤ nablaSq ℂ n mu := inf_le_left
  have hstab : ∀ (g : GL (Fin n) ℂ), ∀ f ∈ U, sqAct ℂ n mu g f ∈ U := by
    rintro g f ⟨hf1, hf2⟩
    refine ⟨(he n mu).2.2 g f hf1, ?_⟩
    have hf2' : φ f = ψ f := by
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf2
      exact hf2
    show sqAct ℂ n mu g f ∈ LinearMap.ker (φ - ψ)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hφ.2 g f hf1, hψ.2 g f hf1, hf2']
  rcases (hI n mu).2.1 U hU hstab with hbot | htop
  · exfalso
    have he_mem : extremal ℂ n mu ∈ U :=
      ⟨extremal_mem_D n mu, by
        show extremal ℂ n mu ∈ LinearMap.ker (φ - ψ)
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hext, sub_self]⟩
    rw [hbot] at he_mem
    exact extremal_ne_D n mu ((Submodule.mem_bot ℂ).mp he_mem)
  · intro s hs
    have hsU : s ∈ U := by rw [htop]; exact hs
    have h2 : s ∈ LinearMap.ker (φ - ψ) := hsU.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    exact h2

theorem fixed_of_eqv_D (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) :
    IsFixedW h lam mu (φ (extremal ℂ n mu)) := by
  have hmem := extremal_mem_D n mu
  refine ⟨fun g hg1 hg2 => ?_, fun t => ?_⟩
  · rw [← hφ.2 g _ hmem, (he n mu).1 g hg1 hg2]
  · rw [← hφ.2 _ _ hmem, (he n mu).2.1 t, map_smul]

theorem equivariant_map_interlacing_unique (hI : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) {n N : ℕ} (h : n + 1 = N)
    (lam : DomWeight N) (mu : DomWeight n)
    (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (hφ : IsEqv h mu lam φ) (hφ' : IsEqv h mu lam φ') (hne : ∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) :
    Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s := by
  have hmem := extremal_mem_D n mu
  have hne' : φ' (extremal ℂ n mu) ≠ 0 := by
    intro h0
    obtain ⟨s, hs, hs0⟩ := hne
    apply hs0
    have h3 := eq_on_of_extremal_D hI he h hφ' (isEqv_zero_D h mu lam) (by rw [h0, LinearMap.zero_apply]) s hs
    rw [h3, LinearMap.zero_apply]
  obtain ⟨⟨c, hc⟩, hint⟩ := ha n N h lam mu (φ (extremal ℂ n mu)) (φ' (extremal ℂ n mu)) (hφ.1 _ hmem)
    (hφ'.1 _ hmem) (fixed_of_eqv_D he h hφ) (fixed_of_eqv_D he h hφ') hne'
  refine ⟨hint, c, fun s hs => ?_⟩
  have h3 := eq_on_of_extremal_D hI he h hφ (isEqv_smul_D h hφ' c) (by rw [LinearMap.smul_apply, hc]) s hs
  rw [h3, LinearMap.smul_apply]

def brSupD {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (_ : IsEqv h mu lam φ), (nablaSq ℂ n mu).map φ

theorem branching_rule_decomposition (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl) (hc : HighestVec) (hd : Realize)
    {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : nablaSq ℂ N lam = brSupD h lam := by
  have hmemS : ∀ (mu : DomWeight n) (hint : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ),
      (nablaSq ℂ n mu).map φ ≤ brSupD h lam :=
    fun mu hint φ hφ => le_iSup_of_le mu (le_iSup_of_le hint (le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)))
  have hle : brSupD h lam ≤ nablaSq ℂ N lam := by
    refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hφ.1 s hs
  have hstab : IsStable h lam (brSupD h lam) := by
    intro g
    have key : brSupD h lam ≤ (brSupD h lam).comap (sqLinD N lam (embGL ℂ n N h g)) := by
      refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨s, hs, rfl⟩
      rw [Submodule.mem_comap, sqLinD_apply, ← hφ.2 g s hs]
      exact hmemS mu hint φ hφ ⟨_, (he n mu).2.2 g s hs, rfl⟩
    intro f hf
    exact key hf
  obtain ⟨W', hW'le, hW'st, hsup, hinf⟩ := hb n N h lam (brSupD h lam) hle hstab
  by_cases hW' : W' = ⊥
  · rw [hW', sup_bot_eq] at hsup
    exact hsup.symm
  · exfalso
    obtain ⟨f, hfW, hf0, mu, hfix⟩ := hc n N h lam W' hW'le hW'st hW'
    obtain ⟨φ, hφ, hφe⟩ := hd n N h lam mu f (hW'le hfW) hfix hf0
    have hint : Interlace h lam mu := (ha n N h lam mu f f (hW'le hfW) (hW'le hfW) hfix hfix hf0).2
    have hfS : f ∈ brSupD h lam := hmemS mu hint φ hφ ⟨_, extremal_mem_D n mu, hφe⟩
    have hfI : f ∈ brSupD h lam ⊓ W' := ⟨hfS, hfW⟩
    rw [hinf] at hfI
    exact hf0 ((Submodule.mem_bot ℂ).mp hfI)

theorem gTBranch_of_steps (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) (hd : Realize) : PI.GTBranch := by
  intro n N hnN lam
  refine ⟨fun mu φ φ' hψ hne => ?_, branching_rule_decomposition he ha hb hc hd hnN lam⟩
  have hφ : IsEqv hnN mu lam φ := hψ φ (by simp)
  have hφ' : IsEqv hnN mu lam φ' := hψ φ' (by simp)
  exact equivariant_map_interlacing_unique h he ha hnN lam mu φ φ' hφ hφ' hne

end PI.WGB
