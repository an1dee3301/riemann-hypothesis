module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  first | exact @GlobalTheory.TwistFormsOrth.orthogonal | exact GlobalTheory.TwistFormsOrth.orthogonal | (intros; apply GlobalTheory.TwistFormsOrth.orthogonal <;> assumption)
