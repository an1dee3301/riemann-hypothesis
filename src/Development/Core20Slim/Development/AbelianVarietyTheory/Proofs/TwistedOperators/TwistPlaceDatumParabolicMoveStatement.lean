module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlaceDatumParabolicMove
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
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

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaceDatum_parabolic_move : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (n : ℤ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Q, G PP ∈ blockTri (blk2 r) ∧ H PP ∈ blockTri (blk2 r)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaQ Q r ξ n (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Q, (ξ PP (Matrix.GeneralLinearGroup.det (G PP)) * (ξ PP (dBlk (blk2 r) 1 (G PP)))⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (H PP)))⁻¹ * ξ PP (dBlk (blk2 r) 1 (H PP)))) ^ n : ℂˣ) : ℂ) * omegaQ Q r ξ n y := by
  first | exact @GlobalTheory.ParabolicDatum.omegaQ_parabolic | exact GlobalTheory.ParabolicDatum.omegaQ_parabolic | (intros; apply GlobalTheory.ParabolicDatum.omegaQ_parabolic <;> assumption)
