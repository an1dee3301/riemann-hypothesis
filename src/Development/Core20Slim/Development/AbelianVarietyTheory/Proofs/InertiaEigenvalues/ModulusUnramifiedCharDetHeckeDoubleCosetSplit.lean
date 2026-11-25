module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetValue

open GlobalTheory.SplitHecke

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))



theorem card_residue_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap F (Fv F v)) v (fun _ => rfl) fun s => by
    rw [hφ, HeightOneSpectrum.intValuation_lt_one_iff_mem]

end Local

section Chart

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}


end Chart



end GlobalTheory.SplitDetValue
