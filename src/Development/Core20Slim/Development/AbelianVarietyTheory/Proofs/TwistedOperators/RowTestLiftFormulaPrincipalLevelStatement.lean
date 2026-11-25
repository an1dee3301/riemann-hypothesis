module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestLiftFormula_principalLevel : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := by
  first | exact @GlobalTheory.RowClaim.FormulaTwo.formula2K | exact GlobalTheory.RowClaim.FormulaTwo.formula2K | (intros; apply GlobalTheory.RowClaim.FormulaTwo.formula2K <;> assumption)
