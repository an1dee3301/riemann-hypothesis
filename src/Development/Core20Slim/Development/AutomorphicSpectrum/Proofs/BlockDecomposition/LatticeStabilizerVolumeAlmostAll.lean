module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasures
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab

section Rows

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_latV_iff_rows {d M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ a, (fun _ : Fin 1 => X a) ∈ latV b v :=
  ⟨fun h a _ i k => h a i k, fun h a i k => h a 0 i k⟩

theorem actW_mem_iff (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J)
    (hg : latStab σ J b v g) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    actW (Fv F v) σ J g X ∈ latV b v ↔ X ∈ latV b v := by
  rw [mem_latV_iff_rows, mem_latV_iff_rows b v X]
  exact forall_congr' fun a => hg fun _ => X a

theorem consA_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (a : Fin 1 → Fin n → Fv F v ⊗[F] E) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    consA a Y ∈ latV b v ↔ a ∈ latV b v ∧ Y ∈ latV b v := by
  constructor
  · intro hX
    refine ⟨fun p j k => ?_, fun j i k => ?_⟩
    · have := hX j.succ 0 k
      rw [Subsingleton.elim p 0]
      simpa [consA] using this
    · have := hX j.succ i.succ.succ k
      simpa [consA] using this
  · rintro ⟨ha, hY⟩ p
    refine Fin.cases ?_ (fun j => ?_) p
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consA] using GlobalTheory.CompanionTheory.SW.LatRat.one_mem_latR h k
      · simp [consA]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consA] using ha 0 j k
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [consA]
        · intro k
          simpa [consA] using hY j i k

end Rows

theorem stageInt_latStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ (m : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)), latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam m ((latV b v).indicator 1) g = m (latV b v) := by
  intro F E _ _ _ _ _ σ hCM M J _ n d b
  have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
      algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => GlobalTheory.CompanionTheory.SW.LatRat.eventually_integral (b.repr (1 : E) k)
  filter_upwards [h0] with v hv
  intro lam hlam m g hg
  classical
  have hmass : coordW (Fv F v) b lam 1 n (latV b v) = 1 := by
    choose std hstd using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
    have hfam : ∀ w, IsStdV w (Function.update std v lam w) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa using hlam
      · simpa [Function.update_of_ne hw] using hstd w
    simpa using GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hCM b (Function.update std v lam) hfam 1 n v
  have hin : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E,
      ∫⁻ a, (latV b v).indicator 1 (actW (Fv F v) σ (hypOne J) g (consA a Y))
        ∂(coordW (Fv F v) b lam 1 n) = (latV b v).indicator 1 Y := by
    intro Y
    by_cases hY : Y ∈ latV b v
    · have hf : (fun a : Fin 1 → Fin n → Fv F v ⊗[F] E =>
          (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ (hypOne J) g (consA a Y))) =
          (latV b v).indicator 1 := by
        funext a
        by_cases ha : a ∈ latV b v
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem
            ((actW_mem_iff σ _ b v g hg _).2 ((consA_mem_iff hv a Y).2 ⟨ha, hY⟩))]
          rfl
        · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem
            fun hc => ha ((consA_mem_iff hv a Y).1 ((actW_mem_iff σ _ b v g hg _).1 hc)).1]
      rw [hf, lintegral_indicator_one (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM b 1 n v), hmass,
        Set.indicator_of_mem hY]
      rfl
    · have hf : (fun a : Fin 1 → Fin n → Fv F v ⊗[F] E =>
          (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ (hypOne J) g (consA a Y))) = 0 := by
        funext a
        exact Set.indicator_of_notMem
          (fun hc => hY ((consA_mem_iff hv a Y).1 ((actW_mem_iff σ _ b v g hg _).1 hc)).2) _
      rw [hf, Set.indicator_of_notMem hY, lintegral_zero_fun]
  unfold stageInt
  simp_rw [hin]
  exact lintegral_indicator_one (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM b n M v)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab
