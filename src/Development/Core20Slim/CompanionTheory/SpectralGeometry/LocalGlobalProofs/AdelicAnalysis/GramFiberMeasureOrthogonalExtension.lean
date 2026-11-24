module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocalStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TupFubini

variable {T : Type} [MeasurableSpace T]

theorem measurable_cons_tail {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) :
    Measurable (fun Y : Fin n → A => (Fin.cons x Y : Fin (n + 1) → A)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using measurable_pi_apply j

theorem piFinSuccAbove_symm_apply {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) (Y : Fin n → A) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).symm (x, Y) = Fin.cons x Y := by
  apply (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).injective
  rw [MeasurableEquiv.apply_symm_apply]
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

theorem lintegral_tuple_succ (m : Measure T) [SigmaFinite m] (n N : ℕ)
    (ψ : (Fin (n + 1) → Fin N → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ X, ψ X ∂(Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin N => m) =
      ∫⁻ y : Fin 1 → Fin N → T, ∫⁻ Y : Fin n → Fin N → T, ψ (Fin.cons (y 0) Y)
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin N => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin N => m) := by
  set P : Measure (Fin N → T) := Measure.pi fun _ : Fin N => m with hP
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
  have h2 := measurePreserving_funUnique P (Fin 1)
  have hg : Measurable fun p : (Fin N → T) × (Fin n → Fin N → T) =>
      ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin N → T) 0).symm p) :=
    hψ.comp (MeasurableEquiv.measurable _)
  rw [← h1.symm.lintegral_comp hψ, lintegral_prod _ hg.aemeasurable,
    ← h2.lintegral_comp hg.lintegral_prod_right']
  refine lintegral_congr fun y => lintegral_congr fun Y => ?_
  rw [piFinSuccAbove_symm_apply]
  rfl

theorem lintegral_tuple_first_coord (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 1) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) =
      ∫⁻ c : Fin n → T, ∫⁻ X : Fin n → Fin M → T, ψ (fun a => Fin.cons (c a) (X a))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin n => m) := by
  let e₁ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => T) 0
  have h₁ : MeasurePreserving e₁ (Measure.pi fun _ : Fin (M + 1) => m)
      (m.prod (Measure.pi fun _ : Fin M => m)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => m) 0
  have h₂ := measurePreserving_pi (fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
    (fun _ : Fin n => m.prod (Measure.pi fun _ : Fin M => m)) (f := fun _ => e₁) (fun _ => h₁)
  have h₃ := measurePreserving_arrowProdEquivProdArrow T (Fin M → T) (Fin n) (fun _ => m)
    (fun _ => Measure.pi fun _ : Fin M => m)
  have h₄ := h₃.comp h₂
  let g : (Fin n → T) × (Fin n → Fin M → T) → Fin n → Fin (M + 1) → T :=
    fun p a => e₁.symm (p.1 a, p.2 a)
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun a => e₁.symm.measurable.comp ?_
    exact ((measurable_pi_apply a).comp measurable_fst).prodMk
      ((measurable_pi_apply a).comp measurable_snd)
  have hgi : ∀ Y, g ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
      fun Y a => e₁ (Y a)) Y) = Y := by
    intro Y
    funext a
    exact e₁.symm_apply_apply (Y a)
  have hψg : Measurable (ψ ∘ g) := hψ.comp hg
  calc ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
      = ∫⁻ Y, (ψ ∘ g) ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
          fun Y a => e₁ (Y a)) Y) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) :=
        lintegral_congr fun Y => by simp only [Function.comp_apply (f := ψ), hgi]
    _ = _ := h₄.lintegral_comp hψg
    _ = _ := lintegral_prod _ hψg.aemeasurable
    _ = _ := by
      refine lintegral_congr fun c => lintegral_congr fun X => ?_
      simp only [Function.comp_apply, g]
      congr 1
      funext a
      exact piFinSuccAbove_symm_apply (c a) (X a)

end GlobalTheory.CompanionTheory.SW.TupFubini

namespace GlobalTheory.CompanionTheory.SW

theorem lintegral_tuple_moving_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR d b lam hlam n s _ φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hact : ∀ h : HA R σ J, Measurable (actW R σ J h :
      (Fin n → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin (M + 1) → R ⊗[F] E) := by
    intro h
    have := hBorel n (M + 1)
    have hc := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) J hJ R).2.2.2.2.2 n).1
    exact (hc.comp (Continuous.prodMk_right h)).measurable
  have key : ∀ y : Fin 1 → Fin (M + 1) → R ⊗[F] E,
      ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1)) =
      ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a))))
        ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) := by
    intro y
    have hinv := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hCM (M + 1) J hJ R hR n (coordW R b lam n (M + 1)) (hW n (M + 1)) (s y)
    have hf : Measurable fun Y : Fin n → Fin (M + 1) → R ⊗[F] E =>
        φ (Fin.cons (y 0) Y) := hφ.comp (TupFubini.measurable_cons_tail (y 0))
    calc ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1))
        = ∫⁻ Y, φ (Fin.cons (y 0) Y) ∂((coordW R b lam n (M + 1)).map (actW R σ J (s y))) := by
          rw [hinv]
      _ = ∫⁻ Y, φ (Fin.cons (y 0) (actW R σ J (s y) Y)) ∂(coordW R b lam n (M + 1)) :=
          lintegral_map hf (hact (s y))
      _ = _ := TupFubini.lintegral_tuple_first_coord (coordK R b lam) n M _ (hf.comp (hact (s y)))
  calc ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y)
          ∂(coordW R b lam n (M + 1)) ∂(coordW R b lam 1 (M + 1)) :=
        TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 1) φ hφ
    _ = _ := lintegral_congr key

end GlobalTheory.CompanionTheory.SW
