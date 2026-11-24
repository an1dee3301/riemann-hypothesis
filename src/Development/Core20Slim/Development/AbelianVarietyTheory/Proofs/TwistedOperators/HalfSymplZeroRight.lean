module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

variable {D : D7}

def halfPair (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AE D :=
  ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j

def halfSympl (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * halfPair W a t)

theorem halfSympl_add_right (W : HSp D) {r : ℕ} (a t t' : Mx D W.rank r) :
    halfSympl W a (t + t') = halfSympl W a t + halfSympl W a t' := by
  simp only [halfSympl, halfPair]
  rw [← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_add]

theorem halfSympl_add_left (W : HSp D) {r : ℕ} (a a' t : Mx D W.rank r) :
    halfSympl W (a + a') t = halfSympl W a t + halfSympl W a' t := by
  simp only [halfSympl, halfPair]
  rw [← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [add_mul]

theorem halfSympl_zero_right (W : HSp D) {r : ℕ} (a : Mx D W.rank r) : halfSympl W a 0 = 0 := by
  simp [halfSympl, halfPair]

theorem halfSympl_zero_left (W : HSp D) {r : ℕ} (t : Mx D W.rank r) : halfSympl W 0 t = 0 := by
  simp [halfSympl, halfPair]

end GlobalTheory.HalfAverage
