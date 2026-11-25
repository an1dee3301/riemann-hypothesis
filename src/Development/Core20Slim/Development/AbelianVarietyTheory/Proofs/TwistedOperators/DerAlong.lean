module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal TensorProduct

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def term (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E) : ℂ :=
  res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G) 0

def phase (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) : ℂ :=
  ψ (symplO V W (isoPart V W C' (Matrix.map y (incA D))) (isoPart V W C κ))

def pairQ (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin W.rank) D.host.E :=
  D.host.xi0 • (adj D y * W.gram)

def ratPair (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) : ℝ :=
  ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * x)) : ℚ) : ℝ)

def dirAt (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin r) ℂ) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  z * (adj D C * V.gram).map (tauE D τ)

def derAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  ∑ τ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G

def finLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 0 1 : AF D.host.F) ⊗ₜ[D.host.F] e

end GlobalTheory.MixedTerm

end
