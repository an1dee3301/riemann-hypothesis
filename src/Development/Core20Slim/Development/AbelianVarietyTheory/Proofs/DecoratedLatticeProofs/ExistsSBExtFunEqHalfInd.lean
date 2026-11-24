module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HalfInd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']








theorem exists_idem (p : SplitPt D k) : ∃ ε, IsPlaceIdem D p.v ε ∧ algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
  obtain ⟨ε, hε, h⟩ := p.above
  exact ⟨ε, hε, by rw [← h, add_mul, p.split.1, mul_comm, p.split.2.1, add_zero]⟩



end GlobalTheory.FinPl.HalfInd

end
