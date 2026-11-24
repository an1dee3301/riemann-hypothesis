module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjLat0
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.Bridge
public import Mathlib
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.LatITopBasis
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.IdealBasis
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

theorem lambda_of_lattice_holds : LamOfLat := by
  intro D cc δ hcc hδ
  exact lattice_ideal_lattice_holds D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩
    (br_sqrt_sq D) (br_finrank_K D) (brPhi D) cc δ hcc hδ




end Formalism.L2.Th1.F2
