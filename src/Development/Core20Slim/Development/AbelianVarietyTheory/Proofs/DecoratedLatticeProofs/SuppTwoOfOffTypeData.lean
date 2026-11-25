module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumRestrictionRankZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualGOfGQ
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDoubleCosetPointsChainPlaceByPlace
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

namespace GlobalTheory.FinPl.SuppTwoAsm

set_option maxHeartbeats 800000 in
theorem ginf_le_grpOff {D : D7} (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  have h1 := Units.ext_iff.mp ha
  simp only [finHom, Formalism.UG.bc, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at h1
  apply Units.ext
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  simp only [MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe] at h2
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe]
  have hf : (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = finPart D := rfl
  rw [hf] at h2
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h2 ⊢
    rw [← map_one (Ideal.Quotient.mk (idOff D P)), Ideal.Quotient.eq, idOff, Ideal.mem_iInf]
    intro w
    have h3 : compAt D w.1 ((matHom V a).val i i) = compAt D w.1 1 := by
      rw [compAt, RingHom.comp_apply, RingHom.comp_apply, h2, RingHom.map_one]
      exact (RingHom.map_one _).symm
    rw [RingHom.mem_ker, RingHom.map_sub, h3, sub_self]
  · rw [Matrix.one_apply_ne hij] at h2 ⊢
    rw [Ideal.Quotient.eq_zero_iff_mem, idOff, Ideal.mem_iInf]
    intro w
    rw [RingHom.mem_ker, compAt, RingHom.comp_apply, h2, map_zero]

end GlobalTheory.FinPl.SuppTwoAsm
