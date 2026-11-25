module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKH.Iwas

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

def sg (v : Pl F) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

theorem ev_sg (a : Fv F v) : evFin F v (sg v a) = a := evalV_singleFin_self v a

theorem mul_sg (u : AF F) (a : Fv F v) : u * sg v a = sg v (evFin F v u * a) := by
  refine Prod.ext (mul_zero _) (af_ext fun t => ?_)
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t (u.2 * singleFin v a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t (singleFin v _)
  by_cases ht : t = v
  · subst ht
    rw [map_mul, evalV_singleFin_self, evalV_singleFin_self]; rfl
  · rw [map_mul, evalV_singleFin_ne ht, evalV_singleFin_ne ht, mul_zero]

theorem at_sg (a : Fv F v) : At (evFin F v) (sg v a) := fun u hu => by
  rw [smul_eq_mul, mul_sg, hu, zero_mul, map_zero]


variable (E) in
def sgE (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (sg v) LinearMap.id

omit [NumberField E] in
theorem comp_sgE (y : Fv F v ⊗[F] E) : compFin F E v (sgE E v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (ev_sg a)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem at_sgE (y : Fv F v ⊗[F] E) : At (evFin F v) (sgE E v y) := fun u hu => by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change (u • sg v a) ⊗ₜ[F] x = 0
    rw [at_sg a u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]

omit [NumberField E] in
theorem sgE_comp (z : AE F E) : sgE E v (compFin F E v z) = sg v 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change sg v (evFin F v a) ⊗ₜ[F] x = (sg v 1 * a) ⊗ₜ[F] x
    rw [mul_comm, mul_sg, mul_one]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

omit [NumberField E] in
theorem eq_zero_of_at {z : AE F E} (hz : At (evFin F v) z) (h : compFin F E v z = 0) : z = 0 := by
  have h1 := hz (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, ← sgE_comp, h, map_zero, sub_zero] at h1
  exact h1

def piE (h : w.under (𝓞 F) = v) : AE F E →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)


theorem piE_cA {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (z : AE F E) :
    piE h (cA σ z) = c (piE h z) := by
  change toCompl h _ = c (toCompl h _)
  rw [hc]
  congr 1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

section Vec

variable {ι : Type}



end Vec

section Mat

variable {ι κ μ : Type}



omit [NumberField E] in
theorem at_sub {X : Type} [AddCommGroup X] [Module (AF F) X] {x y : X} (hx : At (evFin F v) x) (hy : At (evFin F v) y) :
    At (evFin F v) (x - y) := fun u hu => by rw [smul_sub, hx u hu, hy u hu, sub_zero]

omit [NumberField E] in
theorem at_add {X : Type} [AddCommGroup X] [Module (AF F) X] {x y : X} (hx : At (evFin F v) x) (hy : At (evFin F v) y) :
    At (evFin F v) (x + y) := fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

omit [NumberField E] in
theorem at_zero {X : Type} [AddCommGroup X] [Module (AF F) X] : At (evFin F v) (0 : X) := fun u _ => smul_zero u

omit [NumberField E] in
theorem at_mul_left [Fintype κ] {M : Matrix ι κ (AE F E)} (hM : At (evFin F v) M) (N : Matrix κ μ (AE F E)) :
    At (evFin F v) (M * N) := fun u hu => by rw [← Matrix.smul_mul, hM u hu, Matrix.zero_mul]

omit [NumberField E] in
theorem at_mul_right [Fintype κ] (M : Matrix ι κ (AE F E)) {N : Matrix κ μ (AE F E)} (hN : At (evFin F v) N) :
    At (evFin F v) (M * N) := fun u hu => by rw [← Matrix.mul_smul, hN u hu, Matrix.mul_zero]


omit [NumberField E] in
theorem at_mulVec_right [Fintype κ] (M : Matrix ι κ (AE F E)) {y : κ → AE F E} (hy : At (evFin F v) y) :
    At (evFin F v) (M *ᵥ y) := fun u hu => by rw [← Matrix.mulVec_smul, hy u hu, Matrix.mulVec_zero]





end Mat


end PositivityTheory.ThKH.Iwas
