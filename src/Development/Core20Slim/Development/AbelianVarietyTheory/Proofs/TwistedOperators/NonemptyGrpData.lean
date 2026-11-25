module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Formalism.LocalRingCardinality.DataTheta

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.DetSqrtCover

theorem nonempty_grpData : ∀ p q : ℕ, Nonempty (GrpData p q) :=
  fun p q => ⟨grpOf p q MeasureTheory.Measure.haar⟩

end GlobalTheory.DetSqrtCover
