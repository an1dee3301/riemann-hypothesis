module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem star_mulVec_dotProduct_mulVec_mulVec (M H : Matrix ι ι ℂ) (y z : ι → ℂ) :
    star (M *ᵥ y) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star y ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

theorem ArchInvariant.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchInvariant.Statement h v := by
  intro g y z w
  have hmem := mem_archUnitary.mp (g⁻¹ : archUnitary h v).2 w
  set M : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hM
  have hct : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hct] at hmem
  show star (M *ᵥ y w) ⬝ᵥ (gramAt h v w *ᵥ (M *ᵥ z w)) = star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)
  rw [star_mulVec_dotProduct_mulVec_mulVec, hmem]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
