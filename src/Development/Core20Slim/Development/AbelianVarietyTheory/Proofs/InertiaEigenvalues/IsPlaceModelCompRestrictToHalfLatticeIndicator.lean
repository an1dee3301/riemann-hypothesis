module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnitaryVolumePairs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix 
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ExportSeries

namespace RestrictHalfModel

variable {D : D7} {m n : ℕ}

theorem isHalf_iff' (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := GlobalTheory.SplitScalar.isHalf_iff e u

theorem isHalf_smul {e : AE D} (he : e * e = e) (u : Mx D m n) : IsHalf e (e • u) := by
  rw [isHalf_iff', smul_smul, he]


theorem smul_of_half {a' b : AE D} (hab : a' * b = 0) {x : Mx D m n} (hx : IsHalf a' x) :
    b • x = 0 ∧ (a' + b) • x = x := by
  rw [isHalf_iff'] at hx
  have h0 : b • x = 0 := by
    rw [← hx, smul_smul, mul_comm, hab, zero_smul]
  exact ⟨h0, by rw [add_smul, hx, h0, add_zero]⟩

theorem isHalf_add_iff {e : AE D} {t u : Mx D m n} (hu : e • u = u) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [isHalf_iff', isHalf_iff', smul_add, hu, add_left_inj]


end RestrictHalfModel



end GlobalTheory.ExportSeries

end
