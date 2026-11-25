module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroIntSmulMemOfIsLattice
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertSph Matrix Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LatAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_integral (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  a.2.2

theorem smul_mem_latAt (X : Spc F E n) (w : Pl (F := F)) {b : AF F} (hb : evFin F w b ∈ w.adicCompletionIntegers F)
    {z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : z ∈ latAt X w) : b • z ∈ latAt X w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨b * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hb hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (v : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice L hL v

theorem exists_int_mulVec_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L, c • (N *ᵥ y) ∈ L := by
  have key : ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L', c • (N *ᵥ y) ∈ L := by
    intro L' hL'
    induction L', hL' using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨c, hc, hx⟩ := exists_int_smul_mem L hL (N *ᵥ x)
      refine ⟨c, hc, fun y hy => ?_⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [Matrix.mulVec_smul, smul_comm]
      exact L.smul_mem r hx
    | sup A B _ _ hA hB =>
      obtain ⟨c, hc, hA⟩ := hA
      obtain ⟨d, hd, hB⟩ := hB
      refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Matrix.mulVec_add, smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact zsmul_mem (hA a ha) d
      · rw [mul_smul]; exact zsmul_mem (hB b hb) c
  exact key L hL.fg

theorem eventually_incM (X : Spc F E n) (hL : X.L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, incM F N *ᵥ z ∈ latAt X w := by
  obtain ⟨c, hc, hN⟩ := exists_int_mulVec_mem X.L hL N
  filter_upwards [eventually_integral (algebraMap F (AF F) (c : F)⁻¹)] with w hw z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    have h1 : (a • fun i => inclR (F := F) (AF F) ((c • (N *ᵥ y)) i)) ∈ latAt X w :=
      AddSubgroup.subset_closure ⟨a, ha, hv, _, hN y hy, rfl⟩
    have h2 := smul_mem_latAt X w hw h1
    convert h2 using 1
    rw [Matrix.mulVec_smul, smul_comm]
    congr 1
    ext i
    have hc' : (c : F) ≠ 0 := Int.cast_ne_zero.2 hc
    have h3 : (incM F N *ᵥ fun i => inclR (F := F) (AF F) (y i)) i = inclR (F := F) (AF F) ((N *ᵥ y) i) :=
      (RingHom.map_mulVec (inclR (F := F) (AF F)) N y i).symm
    rw [h3, Pi.smul_apply, Pi.smul_apply, map_zsmul, algebraMap_smul, ← Int.cast_smul_eq_zsmul F, smul_smul,
      inv_mul_cancel₀ hc', one_smul]
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem eventually_single (X : Spc F E n) (hL : X.L.IsFullLattice E) (i j : Fin n) (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, Matrix.single i j t *ᵥ z ∈ latAt X w := by
  induction t using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun w z _ => by simp [zero_mem]
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]
      split_ifs
      · simp [inclR, TensorProduct.smul_tmul']
      · simp
    filter_upwards [eventually_integral a, eventually_incM X hL (Matrix.single i j e)] with w hw h2 z hz
    rw [h, Matrix.smul_mulVec]
    exact smul_mem_latAt X w hw (h2 z hz)
  | add s t hs ht =>
    filter_upwards [hs, ht] with w h1 h2 z hz
    rw [Matrix.single_add, Matrix.add_mulVec]
    exact add_mem (h1 z hz) (h2 z hz)

theorem eventually_mulVec_mem (X : Spc F E n) (hL : X.L.IsFullLattice E) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, M *ᵥ z ∈ latAt X w := by
  have h : ∀ᶠ w : Pl F in cofinite, ∀ i j, ∀ z ∈ latAt X w, Matrix.single i j (M i j) *ᵥ z ∈ latAt X w :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_single X hL i j (M i j)
  filter_upwards [h] with w hw z hz
  rw [Matrix.matrix_eq_sum_single M, Matrix.sum_mulVec]
  refine sum_mem fun i _ => ?_
  rw [Matrix.sum_mulVec]
  exact sum_mem fun j _ => hw i j z hz

theorem exists_finset_keeps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsFullLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  intro F E _ _ _ _ _ σ n X hL g
  have h := (eventually_mulVec_mem X hL (mat g)).and (eventually_mulVec_mem X hL (mat g⁻¹))
  refine ⟨(eventually_cofinite.1 h).toFinset, fun w hw z hz => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
  exact ⟨hw.1 z hz, hw.2 z hz⟩

end GlobalTheory.LatAlmostAll
