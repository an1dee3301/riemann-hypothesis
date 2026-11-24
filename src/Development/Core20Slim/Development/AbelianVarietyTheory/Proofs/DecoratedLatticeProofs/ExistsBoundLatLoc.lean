module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
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
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

noncomputable section

namespace GlobalTheory.LocalLatticeBound

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem abs_zero_le (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : absFin F v (0 : Fv F v ⊗[F] E) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_zero, (absBar_eq_zero F v).2 rfl]; exact zero_le

theorem abs_neg_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {y : Fv F v ⊗[F] E} (h : absFin F v y ≤ C) :
    absFin F v (-y) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_neg, absBar_neg]; exact (le_absFin F v τ y).trans h

theorem abs_int_mul_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {c y : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v)
    (h : absFin F v y ≤ C) : absFin F v (c * y) ≤ C :=
  (absFin_mul_le F v c y).trans ((mul_le_mul' (absFin_le_one_of_mem_intLoc hc) h).trans_eq (one_mul C))

theorem exists_bound_rat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ x ∈ L, ∀ i, absFin F v ((1 : Fv F v) ⊗ₜ[F] x i) ≤ C := by
  obtain ⟨S, rfl⟩ := hL
  refine ⟨S.sup fun s => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i), fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem s hs =>
    exact (Finset.le_sup (f := fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun s : Fin n → E => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) hs)
  | zero => rw [Pi.zero_apply, TensorProduct.tmul_zero]; exact abs_zero_le v _
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, TensorProduct.tmul_add]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    have e : (1 : Fv F v) ⊗ₜ[F] (c • x) i = ((1 : Fv F v) ⊗ₜ[F] (c : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc (one_mem _) c) hx

theorem exists_bound_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i : Fin n, absFin F v (y i) ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_rat L (Submodule.IsLattice.fg (A := E) L) v
  refine ⟨C, fun y hy i => ?_⟩
  change y ∈ AddSubgroup.closure _ at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have e : a ⊗ₜ[F] x i = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]; simp
    change absFin F v (a ⊗ₜ[F] x i) ≤ C
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc ha 1) (hC x hx i)
  | zero => exact abs_zero_le v C
  | add y z _ _ hy hz => exact (absFin_add_le F v _ _).trans (max_le hy hz)
  | neg y _ hy => exact abs_neg_le v hy

end GlobalTheory.LocalLatticeBound

end
