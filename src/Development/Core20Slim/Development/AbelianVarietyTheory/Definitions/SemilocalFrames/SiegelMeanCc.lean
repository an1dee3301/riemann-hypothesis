module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

@[expose] public section

open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

def OneVectorCc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    SW1a1 F E σ M J ∧
    (3 ≤ M → ∀ (β : F), β ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
      (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin 1 → Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φi → HasCompactSupport Φi →
      (∀ (N : ℕ) (e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φi ∘ e.symm)) →
      IsPureFin b Φf Φv → IsProdInfFin Φ Φi Φf →
      AllSome (IsCharAF F) fun ψ =>
      OnH F E σ M J fun μ 𝓕 =>
      OnSD F E σ M J ψ 1 (Ainf F) (Fv F) (fun s t => psiInf F ψ (s * t)) (fun v s t => psiV F ψ v (s * t))
        fun μi νi μv νv =>
        ∃ (Fi : Ainf F → ℂ) (Fl : ∀ v, Fv F v → ℂ),
          IsContDensityOn μi (fun X => qR (Ainf F) σ J (X 0)) id νi {c | IsUnit c} Φi Fi ∧
          (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) ∧
          Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) ∧
          meanC μ 𝓕 (thSum F E σ M J Φ {x | hE σ J (x 0) (x 0) = algebraMap F E β}) =
            Fi (algebraMap F (Ainf F) β) * ∏' v, Fl v (algebraMap F (Fv F v) β))



end GlobalTheory.GaussMean
