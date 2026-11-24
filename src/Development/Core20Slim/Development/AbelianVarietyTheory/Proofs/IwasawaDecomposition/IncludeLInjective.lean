module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Formalism.LocalToGlobal.Divisibility.CoefMod

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.Aut Formalism.BasicNotions

namespace GlobalTheory.AlgWtF

section Rat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}











end Rat

section Rep

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

instance finVV (lam : ι → DomWeight n) : FiniteDimensional K (Formalism.L2.DIV.VV K lam) :=
  Module.Finite.of_basis (Formalism.L2.DIV.bVV K lam)

instance finDualVV (lam : ι → DomWeight n) : FiniteDimensional K (Module.Dual K (Formalism.L2.DIV.VV K lam)) := inferInstance





end Rep

end GlobalTheory.AlgWtF
