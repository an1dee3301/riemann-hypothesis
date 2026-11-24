module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Batteries.Logic
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FockOrthogonalDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.VacRead

variable {D : D7}

theorem eq_of_comp {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (w w' : Mx D m n)
    (hw : w.map (finPart D) = 0) (hw' : w'.map (finPart D) = 0) (h : ∀ τ, compAt θ τ w = compAt θ τ w') : w = w' := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have e1 : finPart D (w i j) = 0 := congrFun (congrFun hw i) j
    have e2 : finPart D (w' i j) = 0 := congrFun (congrFun hw' i) j
    rw [RingHom.map_sub, e1, e2, sub_zero]
  · have e : θ τ (infPart D (w i j)) = θ τ (infPart D (w' i j)) := congrFun (congrFun (h τ) i) j
    rw [RingHom.map_sub, RingHom.map_sub, e, sub_self]

theorem realPt_eq {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (w : Mx D m n)
    (hw : w.map (finPart D) = 0) (hz : ∀ τ, compAt θ τ w = z τ) : realPt θ z = w := by
  have hs : (realPt θ z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (realPt θ z) = z τ := by
    unfold realPt
    exact Classical.epsilon_spec (p := fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ) ⟨w, hw, hz⟩
  exact eq_of_comp hθ _ _ hs.1 hw fun τ => (hs.2 τ).trans (hz τ).symm

theorem hAt_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (τ : D.what₂.Tau)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ x y = ∑ i, ∑ j, x i j * starRingEnd ℂ (y i j) := by
  have h1 : gramAt D S τ = 1 := by
    unfold gramAt; rw [hS]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : gramAt D T τ = 1 := by
    unfold gramAt; rw [hT]; exact Matrix.map_one _ (map_zero _) (map_one _)
  unfold GlobalTheory.VacUnique.hAt
  rw [h1, h2, inv_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}


end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead

theorem key_sum {ι : Type} [Fintype ι] (r0 k : ℝ) (s : ι → ℂ) :
    ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * s τ).re : ℝ) : ℂ) +
      Complex.I * ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * (-Complex.I * s τ)).re : ℝ) : ℂ) =
      2 * Complex.I * ((r0 * k : ℝ) : ℂ) * ∑ τ, s τ := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem scale_eq (x y sc : ℝ) (hy : y ≠ 0) (h : sc * y = 2 * x) : x * y⁻¹ = sc / 2 := by
  field_simp
  linarith

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}
open GlobalTheory.FockCompare


end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead


end GlobalTheory.AdForm.VacRead
