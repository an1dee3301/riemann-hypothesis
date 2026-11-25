module
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.OfFn
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs


@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open Filter Topology Set Metric
open scoped ContDiff TensorProduct

namespace Formalism.IndefR.SchurOrthogonalityAlt

section GenAdd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open scoped InnerProductSpace

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]






end GenAdd

section GvPairSec

attribute [local instance] Formalism.BasicNotions.Host.cmStar Matrix.normedAddCommGroup Matrix.normedSpace

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem gp_exp_mem (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hl : (t • X)ᴴ * gramAt D V τ + gramAt D V τ * (t • X) = 0 := by
    have h := CCRuleCW.lie_smul (gramAt D V τ) X hX t
    simpa only [Complex.coe_smul] using h
  exact CCRuleCW.exp_mem_UH (gramAt D V τ) (t • X) hl



theorem gp_exp_split {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ) :
    NormedSpace.exp ((a + b) • X) = NormedSpace.exp (a • X) * NormedSpace.exp (b • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left a).smul_right b)





theorem gp_sv_add {M : DSModel V S} {τ : D.what₂.Tau} {v w : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) (hw : SmoothVec (lieAt V τ) (M.rep τ) w) :
    SmoothVec (lieAt V τ) (M.rep τ) (v + w) := by
  intro k Xs hXs
  simpa only [map_add (f := _)] using (hv k Xs hXs).add (hw k Xs hXs)

theorem gp_sv_smul {M : DSModel V S} {τ : D.what₂.Tau} (c : ℂ) {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) : SmoothVec (lieAt V τ) (M.rep τ) (c • v) := by
  intro k Xs hXs
  simpa only [map_smul] using (hv k Xs hXs).const_smul c

theorem gp_sv_zero {M : DSModel V S} {τ : D.what₂.Tau} : SmoothVec (lieAt V τ) (M.rep τ) (0 : M.H τ) := by
  intro k Xs hXs
  simp only [map_zero]
  exact contDiff_const

theorem gp_sv_of_mem {M : DSModel V S} {τ : D.what₂.Tau} {w : M.H τ} (hw : w ∈ M.sm τ) :
    SmoothVec (lieAt V τ) (M.rep τ) w := by
  have hw' : w ∈ Submodule.span ℂ {w | SmoothVec (lieAt V τ) (M.rep τ) w} := hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact gp_sv_zero
  | add x y _ _ hx hy => exact gp_sv_add hx hy
  | smul c x _ hx => exact gp_sv_smul c hx


































end GvPairSec

end Formalism.IndefR.SchurOrthogonalityAlt

end
