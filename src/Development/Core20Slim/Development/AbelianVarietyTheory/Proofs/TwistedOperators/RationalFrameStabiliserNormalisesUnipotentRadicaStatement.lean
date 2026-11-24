module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadica
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧ (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) → n₀ * L = L) := by
  first | exact @GlobalTheory.FrameStab.stab | exact GlobalTheory.FrameStab.stab | (intros; apply GlobalTheory.FrameStab.stab <;> assumption)
