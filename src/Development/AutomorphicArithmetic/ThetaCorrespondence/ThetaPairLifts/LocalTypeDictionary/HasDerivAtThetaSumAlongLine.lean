module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtThetaSumAlongLineYDirection

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDerFirst
theorem hasDerivAt_thetaSum_along_line : FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (m : ℕ) (f f₁ : Fin m → IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (WeilM.thetaSum F (M.co.rho ψ u (∑ i, IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hG hW γ hγ m f f₁ φ hφ hD u
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ i (g : IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ WeilM.schA F (Fin n × Fin d) :=
    fun i g => TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)
  have hpres := (WeilM.IsUWeilPair.isUSplitting hW).pres
  have hcurve : (fun t : ℝ => WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      = fun t => ∑ i, WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (IndefiniteRowSideFullHecke.WeilTensorModels.tens (IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hpres _ _ (hmem i (f i)))
  have hend : WeilM.thetaSum F (M.co.rho ψ u (∑ i, IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) =
      ∑ i, WeilM.thetaSum F (M.co.rho ψ u
          (IndefiniteRowSideFullHecke.WeilTensorModels.tens (IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j)))) :=
    ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hmem i (f₁ i))
  have hi : ∀ i, HasDerivAt (fun t : ℝ => WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (IndefiniteRowSideFullHecke.WeilTensorModels.tens (IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))))
      (WeilM.thetaSum F (M.co.rho ψ u
                   (IndefiniteRowSideFullHecke.WeilTensorModels.tens (IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) 0 :=
    fun i => T.thetaSum_differentiable_along_line hP M ψ χX χW om hψ hG hW γ hγ (f i) (f₁ i) _
      (ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)) (hD i) u
  rw [hcurve, hend]
  have := HasDerivAt.sum (u := Finset.univ) fun i _ => hi i
  simpa [Finset.sum_fn] using this
end GlobalTheory.ThetaLineDerFirst
end
end
