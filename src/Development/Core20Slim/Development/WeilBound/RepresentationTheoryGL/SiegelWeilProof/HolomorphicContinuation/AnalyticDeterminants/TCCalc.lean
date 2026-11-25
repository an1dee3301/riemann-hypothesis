module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.CompTypeclasses
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped ContDiff
open Set Filter Topology

namespace PositivityTheory.Rg.Sw.LVs.TC

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma iter_smooth {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) :
    ContDiffOn ℂ ∞ (iteratedFDeriv ℂ i F) Ω := by
  intro y hy
  have hle : (∞ : WithTop ℕ∞) + i ≤ ∞ := by
    exact_mod_cast (le_top : (⊤ : ℕ∞) + i ≤ ⊤)
  exact ((hF.contDiffAt (hΩ.mem_nhds hy)).iteratedFDeriv_right hle).contDiffWithinAt

lemma iter_diffAt {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) {y : V} (hy : y ∈ Ω) :
    DifferentiableAt ℂ (iteratedFDeriv ℂ i F) y := by
  exact ((iter_smooth hΩ hF i).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)

lemma iter_cast {F : V → ℂ} {c : V} {m m' : ℕ} (h : m = m') (v : Fin m → V) :
    iteratedFDeriv ℂ m F c v = iteratedFDeriv ℂ m' F c (v ∘ Fin.cast h.symm) := by
  subst h; rfl

end

theorem iterAffine : IterAffine := by
  intro V W _ _ _ _ F Ω hΩ hF c hc L k
  have hT : Continuous (fun y : V => c + y) := continuous_const.add continuous_id
  have hΩ1 : IsOpen ((fun y : V => c + y) ⁻¹' Ω) := hΩ.preimage hT
  have hΩ2 : IsOpen (L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω)) := hΩ1.preimage L.continuous
  have hG : ContDiffOn ℂ ∞ (fun y : V => F (c + y)) ((fun y : V => c + y) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun y hy => hy)
  have hm2 : (0 : W) ∈ L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω) := by simpa using hc
  have hm1 : L 0 ∈ (fun y : V => c + y) ⁻¹' Ω := by simpa using hc
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hG hΩ1.uniqueDiffOn
    hΩ2.uniqueDiffOn hm1 hk
  rw [iteratedFDerivWithin_of_isOpen k hΩ2 hm2, iteratedFDerivWithin_of_isOpen k hΩ1 hm1,
    iteratedFDeriv_comp_add_left] at h1
  simp only [map_zero, add_zero] at h1
  exact h1

def predPerm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) : Equiv.Perm (Fin k) where
  toFun i := (σ i.succ).pred (fun h => Fin.succ_ne_zero i (σ.injective (h.trans h0.symm)))
  invFun i := (σ⁻¹ i.succ).pred (fun h => by
    have : σ⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, h0]
    exact Fin.succ_ne_zero i ((σ⁻¹).injective (h.trans this.symm)))
  left_inv i := by simp
  right_inv i := by simp

lemma predPerm_succ {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (i : Fin k) :
    (predPerm σ h0 i).succ = σ i.succ := by
  simp [predPerm]

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma symm_fix {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    (ih : ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v)
    {c : V} (hc : c ∈ Ω) (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (v : Fin (k + 1) → V) :
    iteratedFDeriv ℂ (k + 1) F c (v ∘ σ) = iteratedFDeriv ℂ (k + 1) F c v := by
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k F) c := iter_diffAt hΩ hF k hc
  have ht : Fin.tail (v ∘ σ) = Fin.tail v ∘ predPerm σ h0 := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [predPerm_succ]
  have h0' : (v ∘ σ) 0 = v 0 := by simp [h0]
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, ht, h0',
    ← fderiv_continuousMultilinear_apply_const_apply hd,
    ← fderiv_continuousMultilinear_apply_const_apply hd]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hΩ.mem_nhds hc] with y hy
  exact ih y hy (Fin.tail v) (predPerm σ h0)

private theorem iteratedFDeriv_add_two_apply {F : V → ℂ} (k : ℕ) (c : V) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c v =
      fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k F)) c (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
  simp [LinearIsometryEquiv.comp_fderiv, Fin.tail]

lemma symm_swap {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    {c : V} (hc : c ∈ Ω) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℂ (k + 2) F c v := by
  have hG : ContDiffAt ℂ ∞ (iteratedFDeriv ℂ k F) c :=
    (iter_smooth hΩ hF k).contDiffAt (hΩ.mem_nhds hc)
  have hmin : minSmoothness ℂ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hs := hG.isSymmSndFDerivAt hmin
  have htt : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [Fin.ext_iff]
  rw [iteratedFDeriv_add_two_apply, iteratedFDeriv_add_two_apply, htt]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hs (v 1) (v 0)]

end

theorem iterSymm : IterSymm := by
  intro V _ _ F Ω hΩ hF
  suffices h : ∀ k : ℕ, ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)),
      iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v from
    fun c hc k v σ => h k c hc v σ
  intro k
  induction k with
  | zero =>
    intro c hc v σ
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    intro c hc v σ
    have key : ∀ (j : Fin (k + 1)) (u : Fin (k + 1) → V),
        iteratedFDeriv ℂ (k + 1) F c (u ∘ Equiv.swap 0 j) = iteratedFDeriv ℂ (k + 1) F c u := by
      intro j u
      by_cases hj0 : j = 0
      · subst hj0
        simp
      · cases k with
        | zero => exact absurd (Fin.fin_one_eq_zero j) hj0
        | succ m =>
          by_cases hj1 : j = 1
          · subst hj1
            exact symm_swap hΩ hF hc u
          · have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
            have hs : Equiv.swap (0 : Fin (m + 2)) j =
                Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j := by
              rw [Equiv.swap_mul_swap_mul_swap h01 (Ne.symm hj0), Equiv.swap_comm]
            have hfix : ∀ w : Fin (m + 2) → V,
                iteratedFDeriv ℂ (m + 2) F c (w ∘ Equiv.swap 1 j) = iteratedFDeriv ℂ (m + 2) F c w :=
              fun w => symm_fix hΩ hF ih hc (Equiv.swap 1 j)
                (Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)) w
            have hcomp : u ∘ ⇑((Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j :
                Equiv.Perm (Fin (m + 2)))) =
                ((u ∘ Equiv.swap 1 j) ∘ Equiv.swap 0 1) ∘ Equiv.swap 1 j := by
              funext i
              simp [Equiv.Perm.mul_apply]
            rw [hs, hcomp, hfix, symm_swap hΩ hF hc, hfix]
    have h0 : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      simp [Equiv.Perm.mul_apply]
    have hv : v ∘ σ = (v ∘ Equiv.swap 0 (σ 0)) ∘ ⇑(Equiv.swap 0 (σ 0) * σ) := by
      funext i
      simp [Equiv.Perm.mul_apply]
    rw [hv, symm_fix hΩ hF ih hc _ h0, key]

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma eval_smooth {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (b : ℕ) (w : Fin b → V) :
    ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x w) Ω :=
  (ContinuousMultilinearMap.apply ℂ (fun _ : Fin b => V) ℂ w).contDiff.comp_contDiffOn (iter_smooth hΩ hF b)

lemma iter_mixed {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (b : ℕ) (w : Fin b → V) :
    ∀ (a : ℕ) {c : V}, c ∈ Ω → ∀ (u : Fin a → V),
      iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) c u = iteratedFDeriv ℂ (a + b) F c (Fin.append u w) := by
  intro a
  induction a with
  | zero =>
    intro c hc u
    rw [iteratedFDeriv_zero_apply, iter_cast (zero_add b) (Fin.append u w),
      Fin.append_left_nil u w rfl]
    congr 1
  | succ a ih =>
    intro c hc u
    have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x w) Ω := eval_smooth hΩ hF b w
    have hd1 := iter_diffAt hΩ hg a hc
    have hd2 := iter_diffAt hΩ hF (a + b) hc
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd1]
    have he : (fun y => iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) y (Fin.tail u))
        =ᶠ[𝓝 c] (fun y => iteratedFDeriv ℂ (a + b) F y (Fin.append (Fin.tail u) w)) := by
      filter_upwards [hΩ.mem_nhds hc] with y hy
      exact ih hy (Fin.tail u)
    rw [he.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply hd2]
    have hs := iteratedFDeriv_succ_apply_left (𝕜 := ℂ) (f := F) (x := c) (n := a + b)
      (Fin.cons (u 0) (Fin.append (Fin.tail u) w))
    rw [Fin.cons_zero, Fin.tail_cons] at hs
    rw [← hs, iter_cast (show a + 1 + b = a + b + 1 by omega) (Fin.append u w)]
    congr 1
    conv_rhs => rw [← Fin.cons_self_tail u, Fin.append_cons]
    funext i
    simp

end

theorem iterNested : IterNested := by
  intro V W1 W2 _ _ _ _ _ _ F Ω hΩ hF c hc L1 L2 a b u w
  have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x (fun i => L2 (w i))) Ω :=
    eval_smooth hΩ hF b _
  have hU : ∀ᶠ t1 in 𝓝 (0 : W1), c + L1 t1 ∈ Ω := by
    have hcont : Continuous (fun t1 : W1 => c + L1 t1) := continuous_const.add L1.continuous
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hΩ.mem_nhds hc
  have he : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    filter_upwards [hU] with t1 ht1
    rw [iterAffine V W2 F Ω hΩ hF (c + L1 t1) ht1 L2 b]
    rfl
  have he' : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝[univ] 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    rw [nhdsWithin_univ]
    exact he
  have hE := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℂ) he' he.eq_of_nhds a
  simp only [iteratedFDerivWithin_univ] at hE
  rw [hE, iterAffine V W1 _ Ω hΩ hg c hc L1 a]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact iter_mixed hΩ hF b _ a hc _

end PositivityTheory.Rg.Sw.LVs.TC
