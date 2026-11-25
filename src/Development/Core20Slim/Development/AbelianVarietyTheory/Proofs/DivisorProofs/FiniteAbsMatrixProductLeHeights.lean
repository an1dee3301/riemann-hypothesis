module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem absFin_mul_mul_transpose_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  intro F E _ _ _ _ _ n d g X h v i j
  have hg : ∀ a b, ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b = compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hh : ∀ a b, ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b = compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hG : ∀ a b, absFin F v (compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b
    rw [hg] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hH : ∀ a b, absFin F v (compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) h) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b
    rw [hh] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hX : ∀ a b, absFin F v (compFin F E v (X a b)) ≤ Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
    intro a b
    exact Finset.le_sup (f := fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) (b := (a, b)) (Finset.mem_univ _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine absFin_sum_le F v _ _ fun l _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.transpose_apply, Matrix.mul_apply, map_mul, map_sum]
  refine (absFin_mul_le F v _ _).trans (mul_le_mul' (absFin_sum_le F v _ _ fun k _ => ?_) (hH _ _))
  rw [map_mul]
  exact (absFin_mul_le F v _ _).trans (mul_le_mul' (hG _ _) (hX _ _))

end GlobalTheory
