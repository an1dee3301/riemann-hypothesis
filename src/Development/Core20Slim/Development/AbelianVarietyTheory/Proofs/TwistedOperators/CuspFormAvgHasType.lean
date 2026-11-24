module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

variable {n : ℕ}

theorem mul_inv_mem_UH {G G₀ A B : Mx n} (hB : IsUnit B) (hA : Aᴴ * G * A = G₀) (hB' : Bᴴ * G * B = G₀) :
    A * B⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have h := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB)
  show (A * B⁻¹)ᴴ * G * (A * B⁻¹) = G
  calc (A * B⁻¹)ᴴ * G * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * G * A) * B⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [hA, ← hB']; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h]; simp

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

def uIso (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) : H ≃ₗᵢ[ℂ] H :=
  { toFun := σ a
    invFun := σ b
    map_add' := map_add _
    map_smul' := map_smul _
    left_inv := fun w => by
      show σ b (σ a w) = w
      rw [← sigma_mul hσ hb ha, hba, sigma_one hσ]
    right_inv := fun w => by
      show σ a (σ b w) = w
      rw [← sigma_mul hσ ha hb, hab, sigma_one hσ]
    norm_map' := hσ.2.1 a ha }

theorem uIso_apply (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) (w : H) : uIso hσ ha hb hab hba w = σ a w := rfl

end GlobalTheory.KFinCuspAvgType

end

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

end GlobalTheory.KFinCuspAvgType
