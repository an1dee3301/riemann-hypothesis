module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
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
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem mt_mul'' (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by
  show (matHom V (g * g')).1 = (matHom V g).1 * (matHom V g').1
  rw [map_mul, Units.val_mul]

theorem mt_one'' (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]






theorem gen_eq (α : Af D.host.F) (c x y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * x * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) * incA D x * incA D y := by
  simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}




end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}




end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd


end GlobalTheory.LatMoveStd
