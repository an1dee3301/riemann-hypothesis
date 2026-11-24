module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlacesLocalDatumBlockTriangularLaw
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaces_localDatum_blockTriangular_law : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Q, gS PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, gT PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y' = (∏ PP ∈ Q, (((ξ PP (dBlk (blk2 r) 1 (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (dBlk (blk2 r) 1 (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y := by
  first | exact @GlobalTheory.OmegaTwistLaw.omegaQ_blockTri | exact GlobalTheory.OmegaTwistLaw.omegaQ_blockTri | (intros; apply GlobalTheory.OmegaTwistLaw.omegaQ_blockTri <;> assumption)
