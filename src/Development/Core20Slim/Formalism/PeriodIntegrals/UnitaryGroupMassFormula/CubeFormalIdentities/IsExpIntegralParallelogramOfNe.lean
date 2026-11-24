module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglGram
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.TendstoCofinite
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}

private theorem coeff_embDomain_rename' (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff (α.embDomain e) (rename e F) = coeff α F :=
  coeff_embDomain_rename e F α

private theorem coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) {β : τ →₀ ℕ}
    (hβ : ¬ ∃ α : σ →₀ ℕ, α.embDomain e = β) : coeff β (rename e F) = 0 := by
  apply coeff_rename_eq_zero
  rintro ⟨α, rfl⟩
  exact hβ ⟨α, Finsupp.embDomain_eq_mapDomain _ _⟩

private theorem constantCoeff_rename_embedding (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) :
    constantCoeff (rename e F) = constantCoeff F :=
  constantCoeff_rename e F

theorem good_rename (e : σ ↪ τ) {D : MvPowerSeries σ ℂ_[p]} (hD : Good D) : Good (rename e D) := by
  obtain ⟨h0, hI⟩ := hD
  have h0' : constantCoeff (rename e D) = 0 := by rw [constantCoeff_rename_embedding]; exact h0
  show constantCoeff (rename e D) = 0 ∧ PI.FglGram.IntegralMv (PI.FglGram.expMv (rename e D))
  refine ⟨h0', ?_⟩
  intro β
  by_cases hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β
  · obtain ⟨α, rfl⟩ := hβ
    have hα := hI α
    rw [coeff_expMv_of_le h0 (α.degree + (α.embDomain e).degree)
      (Nat.le_add_right _ _)] at hα
    rw [coeff_expMv_of_le h0' (α.degree + (α.embDomain e).degree)
      (Nat.le_add_left _ _)]
    have hc : ∀ n, coeff (α.embDomain e) (rename e D ^ n) = coeff α (D ^ n) := fun n => by
      rw [← map_pow, coeff_embDomain_rename']
    simp only [hc]
    exact hα
  · rw [coeff_expMv (rename e D) β]
    have hz : ∀ n, coeff β (rename e D ^ n) = 0 := fun n => by
      rw [← map_pow]; exact coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ
    simp only [hz, zero_div, Finset.sum_const_zero]
    simp [PI.FglGram.IsIntP]

private theorem coeff_subst_eq_sum_range_of_degree_le {a : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) (β : τ →₀ ℕ) (N : ℕ) (hN : β.degree ≤ N) :
    coeff β (PowerSeries.subst a g) =
      ∑ n ∈ Finset.range (N + 1), PowerSeries.coeff n g * coeff β (a ^ n) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) ?_]
  · simp only [smul_eq_mul]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    have h0 : coeff β (a ^ n) = 0 := by
      have := coeff_mul_pow_eq_zero ha (1 : MvPowerSeries τ ℂ_[p]) (n := n) (α := β)
        (by omega)
      simpa using this
    rw [h0, smul_zero]

theorem rename_psubst (e : σ ↪ τ) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst a g) = PowerSeries.subst (rename e a) g := by
  have ha' : constantCoeff (rename e a) = 0 := by rw [constantCoeff_rename_embedding]; exact ha
  ext β
  by_cases hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β
  · obtain ⟨α, rfl⟩ := hβ
    rw [coeff_embDomain_rename', coeff_subst_eq_sum_range_of_degree_le ha g α (α.degree + (α.embDomain e).degree)
      (Nat.le_add_right _ _), coeff_subst_eq_sum_range_of_degree_le ha' g _ (α.degree + (α.embDomain e).degree)
      (Nat.le_add_left _ _)]
    have hc : ∀ n, coeff (α.embDomain e) (rename e a ^ n) = coeff α (a ^ n) := fun n => by
      rw [← map_pow, coeff_embDomain_rename']
    simp only [hc]
  · rw [coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ, coeff_subst_eq_sum_range_of_degree_le ha' g β β.degree le_rfl]
    have hz : ∀ n, coeff β (rename e a ^ n) = 0 := fun n => by
      rw [← map_pow]; exact coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ
    simp only [hz, mul_zero, Finset.sum_const_zero]

private theorem constantCoeff_subst_of_zero_lemma_2 {a : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) :
    constantCoeff (PowerSeries.subst a g) = PowerSeries.constantCoeff g := by
  have h := coeff_subst_eq_sum_range_of_degree_le ha g 0 0 (by simp)
  rw [← coeff_zero_eq_constantCoeff_apply, h]
  simp

theorem constantCoeff_log_eq_zero {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have h1 := constantCoeff_subst_of_zero_lemma_2 (τ := Unit) (a := ex) hex l
  rw [h] at h1
  rw [← h1]
  exact PowerSeries.constantCoeff_X

section

variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)

include hl in
theorem cc_lg_add (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (lg l a + lg l b) = 0 := by
  simp only [PI.FglGram.lg]
  rw [map_add (f := _), constantCoeff_subst_of_zero_lemma_2 ha, constantCoeff_subst_of_zero_lemma_2 hb, hl, add_zero]

include hl in
theorem cc_lg_sub (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (lg l a - lg l b) = 0 := by
  simp only [PI.FglGram.lg]
  rw [map_sub, constantCoeff_subst_of_zero_lemma_2 ha, constantCoeff_subst_of_zero_lemma_2 hb, hl, sub_zero]

include hex hl in
theorem rename_phAt_add (e : σ ↪ τ) (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    rename e (phAt ph (add l ex a b)) = phAt ph (add l ex (rename e a) (rename e b)) := by
  have hsum := cc_lg_add hl a b ha hb
  have hF : constantCoeff (PI.FglGram.add l ex a b) = 0 := by
    simp only [PI.FglGram.add, PI.FglGram.pt]
    rw [constantCoeff_subst_of_zero_lemma_2 hsum]
    exact hex
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e hF]
  congr 1
  simp only [PI.FglGram.add, PI.FglGram.pt]
  rw [rename_psubst e hsum, map_add (f := _)]
  simp only [PI.FglGram.lg]
  rw [rename_psubst e ha, rename_psubst e hb]

include hex hl in
theorem rename_phAt_sub (e : σ ↪ τ) (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    rename e (phAt ph (sub l ex a b)) = phAt ph (sub l ex (rename e a) (rename e b)) := by
  have hdif := cc_lg_sub hl a b ha hb
  have hF : constantCoeff (PI.FglGram.sub l ex a b) = 0 := by
    simp only [PI.FglGram.sub, PI.FglGram.pt]
    rw [constantCoeff_subst_of_zero_lemma_2 hdif]
    exact hex
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e hF]
  congr 1
  simp only [PI.FglGram.sub, PI.FglGram.pt]
  rw [rename_psubst e hdif, map_sub]
  simp only [PI.FglGram.lg]
  rw [rename_psubst e ha, rename_psubst e hb]

private theorem rename_embedding_X (e : σ ↪ τ) (i : σ) :
    rename e (X i : MvPowerSeries σ ℂ_[p]) = X (e i) :=
  rename_X e i

theorem rename_phAt_X (e : σ ↪ τ) (i : σ) :
    rename e (phAt ph (Xv (p := p) i)) = phAt ph (Xv (e i)) := by
  have h0 : constantCoeff (PI.FglGram.Xv (p := p) i) = 0 := constantCoeff_X i
  have h1 : rename e (PI.FglGram.Xv (p := p) i) = PI.FglGram.Xv (e i) := rename_embedding_X e i
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e h0, h1]


include hex hl in
theorem isExpIntegral_parallelogram_of_ne (i j : Fin 3) (hij : i ≠ j)
    (hE1 : Simeq (phAt ph (add l ex (Xv 0) (Xv 1)) + phAt ph (sub l ex (Xv 0) (Xv 1)) :
        MvPowerSeries (Fin 2) ℂ_[p]) (2 * phAt ph (Xv 0) + 2 * phAt ph (Xv 1))) :
    Good (phAt ph (add l ex (Xv i) (Xv j)) + phAt ph (sub l ex (Xv i) (Xv j)) -
      (2 * phAt ph (Xv i) + 2 * phAt ph (Xv j)) : MvPowerSeries (Fin 3) ℂ_[p]) := by
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
      | rfl
      | simp_all
  let e : Fin 2 ↪ Fin 3 := ⟨![i, j], hinj⟩
  have c0 : constantCoeff (PI.FglGram.Xv (p := p) (0 : Fin 2)) = 0 := constantCoeff_X _
  have c1 : constantCoeff (PI.FglGram.Xv (p := p) (1 : Fin 2)) = 0 := constantCoeff_X _
  have r0 : rename e (PI.FglGram.Xv (p := p) (0 : Fin 2)) = PI.FglGram.Xv i := rename_embedding_X e 0
  have r1 : rename e (PI.FglGram.Xv (p := p) (1 : Fin 2)) = PI.FglGram.Xv j := rename_embedding_X e 1
  have qa : rename e (PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv (p := p) (0 : Fin 2)) (PI.FglGram.Xv 1))) =
      PI.FglGram.phAt ph (PI.FglGram.add l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by
    rw [rename_phAt_add ph hex hl e _ _ c0 c1, r0, r1]
  have qs : rename e (PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv (p := p) (0 : Fin 2)) (PI.FglGram.Xv 1))) =
      PI.FglGram.phAt ph (PI.FglGram.sub l ex (PI.FglGram.Xv i) (PI.FglGram.Xv j)) := by
    rw [rename_phAt_sub ph hex hl e _ _ c0 c1, r0, r1]
  have q0 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p := p) (0 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv i) :=
    rename_phAt_X ph e 0
  have q1 : rename e (PI.FglGram.phAt ph (PI.FglGram.Xv (p := p) (1 : Fin 2))) = PI.FglGram.phAt ph (PI.FglGram.Xv j) :=
    rename_phAt_X ph e 1
  have h2 := good_rename e ((simeq_iff_good _ _).1 hE1)
  simp only [map_sub, map_add (f := _), map_mul, map_ofNat, qa, qs, q0, q1] at h2
  exact h2

end

theorem cubeRelationOfParallelogram : CubeRelationOfParallelogram := by
  unfold PI.FglGram.CubeRelationOfParallelogram
  intro p _ l ex ph hlep hE1 hE3
  obtain ⟨hex, hX, -⟩ := hlep
  have hl := constantCoeff_log_eq_zero hex hX
  have product_zeroth_first_parts := isExpIntegral_parallelogram_of_ne ph hex hl 0 1 (by decide) hE1
  have sizeConstantAtParamsWeight := isExpIntegral_parallelogram_of_ne ph hex hl 1 2 (by decide) hE1
  have InnerProductFormulaField := isExpIntegral_parallelogram_of_ne ph hex hl 2 0 (by decide) hE1
  have H3 := (simeq_iff_good _ _).1 hE3
  rw [simeq_iff_good]
  have key := (good_sub ((good_sub ((good_sub H3) product_zeroth_first_parts)) sizeConstantAtParamsWeight)) InnerProductFormulaField
  convert key using 1
  ring

end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
