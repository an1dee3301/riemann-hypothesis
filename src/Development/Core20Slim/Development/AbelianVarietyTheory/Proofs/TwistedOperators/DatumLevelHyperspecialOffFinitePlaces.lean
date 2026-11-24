module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OToSAlgebraMap

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.LevelOff

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]




open Filter GlobalTheory.AdelicU

variable {D : D7}


theorem eq_L0sub {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) : Λ = GlobalTheory.LevSplit.L0sub V := by
  obtain ⟨-, -, -, h01, h10⟩ := hB
  ext x
  constructor
  · intro hx
    show x ∈ L0c D V
    simpa using h10 x hx
  · intro hx
    simpa using h01 x hx

theorem finE_mem_St_iff {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) {g : GA D V} (hg : g ∈ GfC V) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ g ∈ KsphC V ∅ := by
  have hfr : Formalism.L2.DIV.IsFrame β (GlobalTheory.LevSplit.L0sub V) := eq_L0sub hB ▸ hB.1
  have e1 := GlobalTheory.LevSplit.mem_St_iff β _ hfr (Formalism.IndefR.Lev.finE V g)
  have e2 := GlobalTheory.LevSplit.ksph_iff V g
  exact e1.trans ⟨fun h => e2.2 ⟨hg, h⟩, fun h => (e2.1 h).2⟩


open Filter GlobalTheory.AdelicU

variable {D : D7}



open GlobalTheory.AdelicU


end GlobalTheory.FinZeta.LevelOff

end
