module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem piW_smul_incl (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (e : E) :
    piW t (a • inclR (F := F) (AF F) e) = evFin F v a * t e := by
  simp [piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]

theorem comp_mem_splitLat (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ L) : (fun i => t (x i)) ∈ splitLat t L := by
  refine ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩
  simp [splitVec, splitProj_tmul]

end GlobalTheory.LatInt

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem map_piW_gen (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    (a • incM F (Matrix.vecMulVec x y)).map (piW t) =
      evFin F v a • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [piW_smul_incl, map_mul]

theorem latAtV_comp_integral {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) :
    ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, x, hx, y, hy, rfl⟩ := hz
    have hx' := (hb.mem_iff).1 (comp_mem_splitLat v t hx)
    have hy' := (hc.mem_iff).1 (comp_mem_splitLat v t hy)
    intro i j
    rw [map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem ha (mul_mem (hx' i) (hy' j))
  | zero => intro i j; simp
  | add γ δ _ _ hγ hδ =>
    intro i j
    rw [Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem (hγ i j) (hδ i j)
  | neg γ _ hγ =>
    intro i j
    rw [Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem (hγ i j)

end GlobalTheory.LatInt
