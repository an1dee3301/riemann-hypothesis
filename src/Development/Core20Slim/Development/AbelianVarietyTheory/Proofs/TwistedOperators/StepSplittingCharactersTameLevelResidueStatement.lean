module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Disjoint
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepSplittingCharacters_tame_levelResidue : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ ∀ (e : AE D) (P : Finset (Pl D.host.E)), (∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) → IsIdemSum e P → TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) ∧ TameOn (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) e P (resChr L t ((j : ℕ) + 1)) := by
  first | exact @GlobalTheory.StepLaw.tameOn_step | exact GlobalTheory.StepLaw.tameOn_step | (intros; apply GlobalTheory.StepLaw.tameOn_step <;> assumption)
