module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnitaryVolumePairs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemOrth
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel        GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PlaceIdemUniq

theorem idemAt_unique_orth : ∀ (D : D7) (a b : AE D) (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt a PP → Formalism.L2.NTheta.IsIdemAt b PP' → (PP = PP' → a = b) ∧ (PP ≠ PP' → a * b = 0) := by
  intro D a b PP PP' ha hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split ha) ha hb
  · exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split ha) ha hb h

end GlobalTheory.PlaceIdemUniq
