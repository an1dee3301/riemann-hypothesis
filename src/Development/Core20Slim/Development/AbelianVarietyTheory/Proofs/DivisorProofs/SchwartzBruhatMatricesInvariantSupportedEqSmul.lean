module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Pi
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SBClosure

open scoped Topology

theorem nonarch_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup (G i)),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

theorem eq_smul_indicator_closure {X : Type} [AddCommGroup X] [TopologicalSpace X] [NonarchimedeanAddGroup X]
    (S : AddSubgroup X) (B : Set X) (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hf0 : f ≠ 0) (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB X, (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) → ∃ c : ℂ, g = c • f) :
    ∃ c : ℂ, f = c • (closure (S : Set X)).indicator 1 ∧ IsOpen (closure (S : Set X)) ∧
      IsCompact (closure (S : Set X)) := by
  set H : AddSubgroup X := S.topologicalClosure with hHdef
  have hHc : (H : Set X) = closure (S : Set X) := rfl
  rw [← hHc]
  have hcont : Continuous f := hf.1.continuous
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (funext h)
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ GlobalTheory.WeilM.SB X, U.indicator φ ∈ GlobalTheory.WeilM.SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hSH : S ≤ H := S.le_topologicalClosure
  have hHcl : IsClosed (H : Set X) := S.isClosed_topologicalClosure
  have hH : ∀ h ∈ H, f (Y₀ + h) = f Y₀ := by
    intro h hh
    have hcl : IsClosed {h : X | f (Y₀ + h) = f Y₀} :=
      isClosed_eq (hcont.comp (continuous_const.add continuous_id)) continuous_const
    have hS : (S : Set X) ⊆ {h : X | f (Y₀ + h) = f Y₀} := fun s hs => hinv s hs Y₀
    exact (closure_minimal hS hcl) hh
  have hW : ∀ x, f x ≠ 0 → x - Y₀ ∈ H := by
    intro x hx
    by_contra hxH
    have hopen : (H : Set X)ᶜ ∈ 𝓝 (x - Y₀) := hHcl.isOpen_compl.mem_nhds hxH
    have h0 : (fun u => x - Y₀ + u) ⁻¹' (H : Set X)ᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      simpa using hopen
    obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    set V : AddSubgroup X := H ⊔ U.toAddSubgroup with hVdef
    have hVo : IsOpen (V : Set X) := AddSubgroup.isOpen_mono (le_sup_right : U.toAddSubgroup ≤ V) U.isOpen
    have hVc : IsClosed (V : Set X) := AddSubgroup.isClosed_of_isOpen V hVo
    have hxV : x - Y₀ ∉ V := by
      intro hm
      obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hm
      have hb' : -b ∈ U := U.neg_mem hb
      have := hU hb'
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe] at this
      apply this
      rw [← hab]
      simpa using ha
    set Wset : Set X := (fun y => y - Y₀) ⁻¹' (V : Set X) with hWdef
    have hWc : IsClopen Wset :=
      ⟨hVc.preimage (continuous_id.sub continuous_const), hVo.preimage (continuous_id.sub continuous_const)⟩
    have hWinv : ∀ s ∈ S, ∀ Y, (Y + s ∈ Wset ↔ Y ∈ Wset) := by
      intro s hs Y
      have hsV : s ∈ V := AddSubgroup.mem_sup_left (hSH hs)
      simp only [Wset, Set.mem_preimage, SetLike.mem_coe]
      rw [show Y + s - Y₀ = (Y - Y₀) + s by abel]
      exact V.add_mem_cancel_right hsV
    obtain ⟨c, hc⟩ := huniq (Wset.indicator f) (hind _ hWc f hf) (by
      intro s hs Y
      by_cases hY : Y ∈ Wset
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem ((hWinv s hs Y).mpr hY), hinv s hs Y]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY ((hWinv s hs Y).mp h))]) (by
      intro Y hY
      by_cases h : Y ∈ Wset
      · rw [Set.indicator_of_mem h, hsupp Y hY]
      · rw [Set.indicator_of_notMem h])
    have e1 := congrFun hc Y₀
    have e2 := congrFun hc x
    have hY₀W : Y₀ ∈ Wset := by simp [Wset, V.zero_mem]
    rw [Set.indicator_of_mem hY₀W] at e1
    rw [Set.indicator_of_notMem (show x ∉ Wset from hxV)] at e2
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    have hc1 : c = 1 := by
      have : (c - 1) * f Y₀ = 0 := by rw [sub_mul, ← e1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hY₀)
    rw [hc1, one_mul] at e2
    exact hx e2.symm
  have hHeq : (H : Set X) = (fun h => Y₀ + h) ⁻¹' {y | f y ≠ 0} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro hh; rw [hH h hh]; exact hY₀
    · intro hne; simpa using hW _ hne
  have hHo : IsOpen (H : Set X) := by
    rw [hHeq]
    exact (isOpen_compl_singleton.preimage hcont).preimage (continuous_const.add continuous_id)
  have hHk : IsCompact (H : Set X) := by
    have hK : IsCompact ((fun h => Y₀ + h) ⁻¹' tsupport f) :=
      (Homeomorph.addLeft Y₀).isCompact_preimage.mpr hf.2
    refine hK.of_isClosed_subset hHcl ?_
    intro h hh
    exact subset_tsupport f (by rw [Function.mem_support, hH h hh]; exact hY₀)
  have hHclo : IsClopen (H : Set X) := ⟨hHcl, hHo⟩
  have h1SB : (H : Set X).indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
    refine ⟨?_, HasCompactSupport.intro' hHk hHcl fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant X ℂ) hHclo).isLocallyConstant
    convert this using 1
    funext x
    first
    | rfl
    | by_cases hx : x ∈ (H : Set X) <;> simp [hx, LocallyConstant.indicator]
  obtain ⟨c, hc⟩ := huniq _ h1SB (by
      intro s hs Y
      have : (Y + s ∈ (H : Set X) ↔ Y ∈ (H : Set X)) := H.add_mem_cancel_right (hSH hs)
      by_cases hY : Y ∈ (H : Set X)
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (this.mpr hY)]; rfl
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (this.mp h))]) (by
      intro Y hY
      refine Set.indicator_of_notMem (fun hYH => hY ?_) _
      have hB0 : Y₀ ∈ B := by
        by_contra h; exact hY₀ (hsupp _ h)
      have hB1 : Y₀ + Y ∈ B := by
        by_contra h; exact hY₀ ((hH Y hYH).symm.trans (hsupp _ h))
      exact hB _ _ hB0 hB1)
  have e0 := congrFun hc 0
  rw [Set.indicator_of_mem (show (0 : X) ∈ (H : Set X) from H.zero_mem)] at e0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at e0
  have hc0 : c ≠ 0 := by
    rintro rfl; simp at e0
  refine ⟨c⁻¹, ?_, hHo, hHk⟩
  funext y
  have ey := congrFun hc y
  simp only [Pi.smul_apply, smul_eq_mul] at ey ⊢
  rw [ey, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.SBClosure

theorem GlobalTheory.SBClosure.main : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {m k : ℕ}
    (S : AddSubgroup (Matrix (Fin m) (Fin k) (Fv F v))) (B : Set (Matrix (Fin m) (Fin k) (Fv F v)))
    (hB : ∀ Y h, Y ∈ B → Y + h ∈ B → h ∈ B) (f : Matrix (Fin m) (Fin k) (Fv F v) → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB _) (hf0 : f ≠ 0)
    (hinv : ∀ s ∈ S, ∀ Y, f (Y + s) = f Y) (hsupp : ∀ Y ∉ B, f Y = 0)
    (huniq : ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin k) (Fv F v)), (∀ s ∈ S, ∀ Y, g (Y + s) = g Y) → (∀ Y ∉ B, g Y = 0) →
      ∃ c : ℂ, g = c • f),
    ∃ c : ℂ, f = c • (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))).indicator 1 ∧
      IsOpen (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) ∧ IsCompact (closure (S : Set (Matrix (Fin m) (Fin k) (Fv F v)))) := by
  intro F _ _ v m k S B hB f hf hf0 hinv hsupp huniq
  haveI : NonarchimedeanAddGroup (Fin k → Fv F v) := GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin k => Fv F v)
  haveI : NonarchimedeanAddGroup (Matrix (Fin m) (Fin k) (Fv F v)) :=
    GlobalTheory.SBClosure.nonarch_pi (fun _ : Fin m => Fin k → Fv F v)
  exact GlobalTheory.SBClosure.eq_smul_indicator_closure S B hB f hf hf0 hinv hsupp huniq
