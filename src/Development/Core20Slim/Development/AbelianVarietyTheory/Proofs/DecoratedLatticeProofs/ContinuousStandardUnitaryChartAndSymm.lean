module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
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
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem continuous_mat_pt (D : D7) (n : ℕ) : Continuous (mat : G D n → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_of_mat_pt {D : D7} {n : ℕ} {X : Type} [TopologicalSpace X] {φ : X → G D n}
    (h : Continuous fun x => mat (φ x)) (h' : Continuous fun x => mat (φ x)⁻¹) : Continuous φ :=
  Continuous.subtype_mk (f := fun x => AdelicU.matHom _ D.sp.cm.sig (Jst D n) (φ x))
    (Units.continuous_iff.2 ⟨h, h'⟩) _

theorem chart_continuous : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hT := (Tm_gram_inv D A μ hμ).2.1
  have h₁ : (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hT, rat_one]
  have h₂ : (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hT, rat_one]
  have e₁ : ∀ g, mat (κ g) = (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) *
      (Formalism.L2.Theta.mt (dblSp A) g * rat (Tm A μ)) := fun g => by
    rw [← hκ g, ← Matrix.mul_assoc, h₁, Matrix.one_mul]
  have e₂ : ∀ x, Formalism.L2.Theta.mt (dblSp A) (κ.symm x) =
      (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat x * rat (Tm A μ)⁻¹ := fun x => by
    have := hκ (κ.symm x)
    rw [κ.apply_symm_apply] at this
    rw [this]
    exact ((Matrix.mul_assoc _ _ _).trans ((congrArg _ h₂).trans (Matrix.mul_one _))).symm
  have c₁ : Continuous fun g => mat (κ g) := by
    simp only [e₁]
    exact continuous_const.matrix_mul ((continuous_mt (dblSp A)).matrix_mul continuous_const)
  refine ⟨continuous_of_mat_pt c₁ ?_, continuous_of_mt (dblSp A) ?_⟩
  · simp only [← map_inv]
    exact c₁.comp continuous_inv
  · simp only [e₂]
    exact (continuous_const.matrix_mul (continuous_mat_pt D A.rank)).matrix_mul continuous_const

end GlobalTheory.StdUnn
