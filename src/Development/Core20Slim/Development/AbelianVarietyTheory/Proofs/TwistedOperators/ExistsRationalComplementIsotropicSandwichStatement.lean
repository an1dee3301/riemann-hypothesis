module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_complement_isotropic_sandwich : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ z : Mx D 1 k, (∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.cplx V W B c)) = 1) ↔ z ∈ GlobalTheory.MixModel.ratMx D 1 k) := by
  first | exact @GlobalTheory.IsoCompl.ratCompl | exact GlobalTheory.IsoCompl.ratCompl | (intros; apply GlobalTheory.IsoCompl.ratCompl <;> assumption)
