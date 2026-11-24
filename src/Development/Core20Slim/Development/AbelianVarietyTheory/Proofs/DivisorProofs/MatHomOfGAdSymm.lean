module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.IwLine

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]


variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)





end GlobalTheory.IwLine
