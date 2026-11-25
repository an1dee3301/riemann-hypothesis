module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical


open Matrix in
theorem GlobalTheory.CuspGK.inK_inv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GlobalTheory.CuspGK.InK M τ g) :
    GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  obtain ⟨hU, hK1, hK2⟩ := h
  set P := M.fr τ with hPdef
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set u := P * g * P⁻¹ with hu
  have huu : IsUnit u.det := Matrix.UnitaryGroup.det_isUnit ⟨u, hK1⟩
  have hg : IsUnit g.det := by
    have hdet : u.det = P.det * g.det * P⁻¹.det := by simp [hu, Matrix.det_mul]
    rw [hdet] at huu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left huu)
  have hinv : P * g⁻¹ * P⁻¹ = u⁻¹ := by
    rw [hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc]
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem hK1
  have hustar : u⁻¹ = star u := Matrix.inv_eq_left_inv hsu
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ huu
  have h2 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ huu
  refine ⟨⟨?_, ?_, ?_⟩, Matrix.nonsing_inv_nonsing_inv _ hg⟩
  · have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
    show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hgg]; simp
  · show P * g⁻¹ * P⁻¹ ∈ _
    rw [hinv, hustar]
    exact Unitary.star_mem hK1
  · show P * g⁻¹ * P⁻¹ * _ = _ * (P * g⁻¹ * P⁻¹)
    rw [hinv]
    clear_value u
    calc u⁻¹ * Formalism.REAL.Jm (M.ε τ) = u⁻¹ * Formalism.REAL.Jm (M.ε τ) * (u * u⁻¹) := by rw [h2, Matrix.mul_one]
      _ = u⁻¹ * (Formalism.REAL.Jm (M.ε τ) * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * Formalism.REAL.Jm (M.ε τ)) * u⁻¹ := by rw [hK2]
      _ = (u⁻¹ * u) * Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by rw [h1, Matrix.one_mul]
