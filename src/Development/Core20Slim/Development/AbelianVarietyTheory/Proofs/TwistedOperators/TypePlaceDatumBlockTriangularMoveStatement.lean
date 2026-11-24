module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlaceDatumBlockTriangularMove
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
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
public import Mathlib.Data.Finset.Range
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
theorem _root_.GlobalTheory.T.typePlaceDatum_blockTriangular_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, G PP ∈ blockTri (blkOf r t) ∧ H PP ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha (G PP) = upperLeftBlock hb (H PP)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP))) * (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))⁻¹ * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹)) : ℂˣ) : ℂ) * omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) y := by
  first | exact @GlobalTheory.StepLaw.omegaG_blockTri_move | exact GlobalTheory.StepLaw.omegaG_blockTri_move | (intros; apply GlobalTheory.StepLaw.omegaG_blockTri_move <;> assumption)
