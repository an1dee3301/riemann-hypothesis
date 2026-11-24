module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionA
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionB
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionC
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionD
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA

@[expose] public section

theorem gelfand_tsetlin_branching : PI.GTBranch :=
  PI.WGB.gTBranch_of_steps highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
    PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists
    (PI.WGB.realize_of highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
      PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists)
