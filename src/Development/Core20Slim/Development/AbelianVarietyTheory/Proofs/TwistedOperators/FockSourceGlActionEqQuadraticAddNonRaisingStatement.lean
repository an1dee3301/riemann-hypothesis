module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSourceGlActionEqQuadraticAddNonRaising
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSourceGlAction_eq_quadratic_add_nonRaising : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (X : Matrix (Fin a) (Fin a) ℂ), 0 < b → (∃ j k, ε j ≠ ε k ∧ X j k ≠ 0 ∧ X k j ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' X = LinearMap.mulLeft ℂ Q + L := by
  first | exact @GlobalTheory.Chain.RealIt.FockSrcDec.fockS_decomp | exact GlobalTheory.Chain.RealIt.FockSrcDec.fockS_decomp | (intros; apply GlobalTheory.Chain.RealIt.FockSrcDec.fockS_decomp <;> assumption)
