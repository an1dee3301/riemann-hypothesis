module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.SatakeDualWeyl.Statement
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
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj.SumModel

open GlobalTheory.ChiGrid Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem readOK {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) : ReadOK σ := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ Φ fun F => (h F _).2 rfl

theorem finEmb_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) (x : GfC B)
    (h : EmbRel B A d.ι x.1 y.1) : finEmb d y = x :=
  Subtype.ext ((GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1).unique (finEmb_rel d y) h)

theorem finEmb_mul {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y y' : GfC A) :
    finEmb d (y * y') = finEmb d y * finEmb d y' := by
  refine finEmb_eq d _ _ ⟨?_, fun v hv => ?_⟩
  · have h1 := (finEmb_rel d y).1
    have h2 := (finEmb_rel d y').1
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  · have h1 := (finEmb_rel d y).2 v hv
    have h2 := (finEmb_rel d y').2 v hv
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, h2, h1]

end GlobalTheory.FunObj.SumModel

end
