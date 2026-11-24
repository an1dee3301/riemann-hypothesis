module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocalStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtension
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrameStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVector
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
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
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
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

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem lintegral_tuple_vH {T : Type} [MeasurableSpace T] (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 2) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 2) => m) =
      ∫⁻ a : Fin 1 → Fin n → T, ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
        ψ (fun j => vH (a 0 j) (s 0 j) (Y j))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) := by
  have hu : ∀ f : (Fin n → T) → ℝ≥0∞,
      ∫⁻ a : Fin 1 → Fin n → T, f (a 0) ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) =
        ∫⁻ c, f c ∂(Measure.pi fun _ : Fin n => m) := fun f =>
    (measurePreserving_funUnique (Measure.pi fun _ : Fin n => m) (Fin 1)).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) f
  have hc : ∀ c : Fin n → T, Measurable fun X : Fin n → Fin (M + 1) → T =>
      ψ (fun a => Fin.cons (c a) (X a)) := by
    intro c
    refine hψ.comp (measurable_pi_iff.2 fun a => ?_)
    exact (TupFubini.measurable_cons_tail (c a)).comp (measurable_pi_apply a)
  rw [TupFubini.lintegral_tuple_first_coord m n (M + 1) ψ hψ]
  refine Eq.trans ?_ (hu fun c => ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
    ψ (fun j => vH (c j) (s 0 j) (Y j)) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
    ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)).symm
  refine lintegral_congr fun c => ?_
  rw [TupFubini.lintegral_tuple_first_coord m n M _ (hc c)]
  exact (hu fun c' => ∫⁻ Y : Fin n → Fin M → T, ψ (fun j => vH (c j) (c' j) (Y j))
    ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)).symm

theorem lintegral_chartS_of_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ X, ¬ IsUnit (X 0 0) → g X = 0)
    (hc : ∀ x : Fin (M + 2) → R ⊗[F] E, IsUnit (x 0) → ∃ c : HA R σ (hypOne J), ∀ v,
      ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v) :
    ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
        ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ hCM M J hJ).1
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hBK : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hBt := hBorel 1 n
  have hHaar := hW 1 n
  have step : ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y)
        ∂(coordW R b lam n (M + 2)) ∂(coordW R b lam 1 (M + 2)) :=
    TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 2) g hg
  rw [step]
  refine lintegral_congr fun x => ?_
  by_cases hu : IsUnit (x 0 0)
  · obtain ⟨c, hcv⟩ := hc (x 0) hu
    have hact : Measurable (actW R σ (hypOne J) c :
        (Fin n → Fin (M + 2) → R ⊗[F] E) → Fin n → Fin (M + 2) → R ⊗[F] E) := by
      have := hBorel n (M + 2)
      have hcont := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 2) (hypOne J) hJ' R).2.2.2.2.2 n).1
      exact (hcont.comp (Continuous.prodMk_right c)).measurable
    have hinv := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hCM (M + 2) (hypOne J) hJ' R hR n (coordW R b lam n (M + 2)) (hW n (M + 2)) c
    have hf : Measurable fun Y : Fin n → Fin (M + 2) → R ⊗[F] E => g (Fin.cons (x 0) Y) :=
      hg.comp (TupFubini.measurable_cons_tail (x 0))
    have hψ := hf.comp hact
    calc ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) ∂(coordW R b lam n (M + 2))
        = ∫⁻ Y, g (Fin.cons (x 0) Y) ∂((coordW R b lam n (M + 2)).map (actW R σ (hypOne J) c)) := by
          rw [hinv]
      _ = ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c Y)) ∂(coordW R b lam n (M + 2)) :=
          lintegral_map hf hact
      _ = ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
            (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
            ∂(coordW R b lam 1 n) :=
          lintegral_tuple_vH (coordK R b lam) n M _ hψ
      _ = _ := by
          refine lintegral_congr fun a => ?_
          have ht := lintegral_add_right_eq_self (μ := coordW R b lam 1 n)
            (fun s : Fin 1 → Fin n → R ⊗[F] E => ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
              (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M))
            (fun _ j => - (tHalf R σ J (x 0) * a 0 j))
          rw [← ht]
          refine lintegral_congr fun s => lintegral_congr fun Y => ?_
          congr 1
          unfold chartS
          congr 1
          funext j
          simpa [actW, actTup, sub_eq_add_neg] using hcv (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))
  · have h0 : ∀ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) = 0 := fun Y => hg0 _ (by simpa using hu)
    have h1 : ∀ a s Y, g (chartS R σ J x a s Y) = 0 := fun a s Y => hg0 _ (by simpa [chartS] using hu)
    simp [h0, h1]

theorem chartS_lintegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) = ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam g hg hg0
  exact lintegral_chartS_of_unitary F E σ hCM M J hJ R hR n d b lam hlam g hg hg0
    fun x hx => GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary F E σ hCM M J hJ R x hx

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
