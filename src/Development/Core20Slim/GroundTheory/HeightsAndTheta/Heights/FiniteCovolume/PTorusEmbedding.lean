module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusEmbedding
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

namespace TorusEmbedding

section Linear

variable {ι : Type*} [Fintype ι]

def pair (H : Matrix ι ι ℂ) (u z : ι → ℂ) : ℂ := star u ⬝ᵥ (H *ᵥ z)

variable {H : Matrix ι ι ℂ} {X Y : ι → ℂ}

theorem pair_add (u z z' : ι → ℂ) : pair H u (z + z') = pair H u z + pair H u z' := by
  simp [pair, mulVec_add, dotProduct_add]

theorem pair_smul (u z : ι → ℂ) (c : ℂ) : pair H u (c • z) = c * pair H u z := by
  simp [pair, mulVec_smul, dotProduct_smul]

theorem add_pair (u u' z : ι → ℂ) : pair H (u + u') z = pair H u z + pair H u' z := by
  simp [pair, add_dotProduct]

theorem smul_pair (u z : ι → ℂ) (c : ℂ) : pair H (c • u) z = starRingEnd ℂ c * pair H u z := by
  simp [pair, star_smul, smul_dotProduct]

theorem pair_swap (hH : H.IsHermitian) (u z : ι → ℂ) :
    pair H u z = starRingEnd ℂ (pair H z u) := by
  rw [pair, pair, dotProduct_mulVec, ← RCLike.star_def, ← star_dotProduct_star, star_star,
    star_mulVec, hH.eq]

variable [DecidableEq ι]

def torusMat (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (s t : ℂ) : Matrix ι ι ℂ :=
  1 + (s - 1) • vecMulVec X (star Y ᵥ* H) + (t - 1) • vecMulVec Y (star X ᵥ* H)

theorem torusMat_mulVec (s t : ℂ) (z : ι → ℂ) :
    torusMat H X Y s t *ᵥ z = z + ((s - 1) * pair H Y z) • X + ((t - 1) * pair H X z) • Y := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, pair,
    dotProduct_mulVec, op_smul_eq_smul, smul_smul]

theorem torusMat_one_one : torusMat H X Y 1 1 = 1 := by
  simp [torusMat]

theorem pair_Y_torusMat (hYY : pair H Y Y = 0) (hYX : pair H Y X = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H Y (torusMat H X Y s t *ᵥ z) = s * pair H Y z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hYX, hYY]; ring

theorem pair_X_torusMat (hXX : pair H X X = 0) (hXY : pair H X Y = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H X (torusMat H X Y s t *ᵥ z) = t * pair H X z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hXX, hXY]; ring

theorem torusMat_mul (hXX : pair H X X = 0) (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1)
    (hYX : pair H Y X = 1) (s t s' t' : ℂ) :
    torusMat H X Y s t * torusMat H X Y s' t' = torusMat H X Y (s * s') (t * t') := by
  refine mulVec_injective (funext fun z => ?_)
  rw [← mulVec_mulVec, torusMat_mulVec s t, pair_Y_torusMat hYY hYX, pair_X_torusMat hXX hXY,
    torusMat_mulVec s' t', torusMat_mulVec]
  module

theorem torusMat_mulVec_X (hXX : pair H X X = 0) (hYX : pair H Y X = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ X = s • X := by
  rw [torusMat_mulVec, hYX, hXX]; module

theorem torusMat_mulVec_Y (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ Y = t • Y := by
  rw [torusMat_mulVec, hYY, hXY]; module

theorem torusMat_mulVec_orth (s t : ℂ) (z : ι → ℂ) (hX : pair H X z = 0) (hY : pair H Y z = 0) :
    torusMat H X Y s t *ᵥ z = z := by
  rw [torusMat_mulVec, hX, hY]; simp

theorem torusMat_unitary (hH : H.IsHermitian) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (s t : ℂ) (hst : starRingEnd ℂ s * t = 1) :
    (torusMat H X Y s t)ᴴ * H * torusMat H X Y s t = H := by
  have hts : starRingEnd ℂ t * s = 1 := by
    have := congrArg (starRingEnd ℂ) hst
    simpa [mul_comm] using this
  have key : ∀ u z : ι → ℂ, pair H (torusMat H X Y s t *ᵥ u) (torusMat H X Y s t *ᵥ z) =
      pair H u z := by
    intro u z
    conv_lhs => rw [torusMat_mulVec s t u]
    rw [add_pair, add_pair, smul_pair, smul_pair, pair_Y_torusMat hYY hYX,
      pair_X_torusMat hXX hXY, torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul,
      pair_swap hH u X, pair_swap hH u Y]
    simp only [map_mul, map_sub, map_one]
    linear_combination (pair H X z * starRingEnd ℂ (pair H Y u)) * hst +
      (pair H Y z * starRingEnd ℂ (pair H X u)) * hts
  refine mulVec_injective (funext fun z => ?_)
  refine dotProduct_eq _ _ fun u => ?_
  rw [dotProduct_comm, dotProduct_comm (H *ᵥ z)]
  have := key (star u) z
  simp only [pair, star_star] at this
  rw [← this, star_mulVec, star_star]
  simp only [dotProduct_mulVec, vecMul_vecMul]

def torusGL (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (a : ℂˣ) : GL ι ℂ where
  val := torusMat H X Y a (starRingEnd ℂ ↑a⁻¹)
  inv := torusMat H X Y ↑a⁻¹ (starRingEnd ℂ a)
  val_inv := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.mul_inv, ← map_mul, Units.inv_mul, map_one,
      torusMat_one_one]
  inv_val := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.inv_mul, ← map_mul, Units.mul_inv, map_one,
      torusMat_one_one]

end Linear

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W}


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem place_pairs (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    pair (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
  obtain ⟨hxx, hww, hxw⟩ := hp
  have e : ∀ x y, pair (gramAt h v w) (vecAt v x w) (vecAt v y w) = w.embedding (h.toSesq x y) :=
    fun x y => (h1 w x y).symm
  refine ⟨by rw [e, hxx, map_zero], by rw [e, hww, map_zero], by rw [e, hxw, map_one], ?_⟩
  rw [pair_swap (h2 w).1, e, hxw, map_one, map_one]

variable (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
  (hp : IsHyperbolicPair h x₀ w₀)

def torusAt (w : InfinitePlace E) (a : ℂˣ) : GL ι ℂ :=
  torusGL (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) (place_pairs h1 h2 hp w).1
    (place_pairs h1 h2 hp w).2.1 (place_pairs h1 h2 hp w).2.2.1 (place_pairs h1 h2 hp w).2.2.2 a

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem torusAt_mem (a : InfinitePlace E → ℂˣ) :
    (fun w => torusAt h1 h2 hp w (a w)) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  have hc : ∀ M : Matrix ι ι ℂ, (M.map (starRingEnd ℂ))ᵀ = Mᴴ := fun M => by
    ext i j; simp [conjTranspose_apply]
  rw [hc]
  refine torusMat_unitary (h2 w).1 hXX hYY hXY hYX _ _ ?_
  rw [← map_mul, Units.mul_inv, map_one]

def torusHom : (InfinitePlace E → ℂˣ) →* archUnitary h v where
  toFun a := ⟨fun w => torusAt h1 h2 hp w (a w), torusAt_mem h1 h2 hp a⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (by
    simp [torusAt, torusGL, torusMat_one_one]))
  map_mul' a b := Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
    simp only [torusAt, torusGL, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
    rw [torusMat_mul hXX hYY hXY hYX, ← map_mul, ← Units.val_mul, ← Units.val_mul,
      ← _root_.mul_inv_rev, mul_comm (b w)]))

theorem continuous_torusHom : Continuous (torusHom h1 h2 hp) := by
  refine Continuous.subtype_mk (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) (a w : ℂ) (starRingEnd ℂ ↑(a w)⁻¹)
    unfold torusMat
    fun_prop
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) ↑(a w)⁻¹ (starRingEnd ℂ (a w : ℂ))
    unfold torusMat
    fun_prop

end Places

section Main

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proof (h : HermitianForm F E W) (v : Basis ι E W) (h1 : HermAtPlace.Statement h v)
    (h2 : GramAtData.Statement h v) : TorusEmbedding.Statement h v := by
  intro x₀ w₀ hp
  refine ⟨torusHom h1 h2 hp, continuous_torusHom h1 h2 hp, fun a w => ?_⟩
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  refine ⟨torusMat_mulVec_X hXX hYX _ _, ?_, fun z hX hY => torusMat_mulVec_orth _ _ z hX hY⟩
  change torusMat _ _ _ _ _ *ᵥ _ = _
  rw [torusMat_mulVec_Y hYY hXY, Units.val_inv_eq_inv_val, map_inv₀]

end Main

end TorusEmbedding

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
