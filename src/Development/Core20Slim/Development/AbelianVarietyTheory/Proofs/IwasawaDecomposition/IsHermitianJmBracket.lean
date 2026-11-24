module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isHermitian_Jm_bracket {n : ℕ} (ε : Fin n → Bool) : (Jm ε).IsHermitian := by
  unfold Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem dRep_bracket : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ w, Sm ε σ w → ∀ X ∈ lieSet ε, ∀ Y ∈ lieSet ε, dRep σ X (dRep σ Y w) - dRep σ Y (dRep σ X w) = dRep σ (X * Y - Y * X) w := by
  intro n ε H _ _ _ σ h w hw X hX Y hY
  have hd : (Jm ε).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)).ne_zero
  have key := fun v (hv : Sm ε σ v) =>
    GlobalTheory.HolDict.LieAct.main n (Jm ε) H σ (isHermitian_Jm_bracket ε) hd h.1 v v hv hv
  have hB : X * Y - Y * X ∈ lieSet ε := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
    show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
    noncomm_ring
  have hXw : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  have hYw : Sm ε σ (dRep σ Y w) := dRep_mem (isUnit_Jm ε) h.1 hw hY
  have e := ((key w hw).1 0 X Y).2.2
  rw [(key w hw).2.1 _ hB, (key w hw).2.1 X hX, (key w hw).2.1 Y hY, (key _ hXw).2.1 Y hY,
    (key _ hYw).2.1 X hX] at e
  exact e.symm

end GlobalTheory.TypeSum
