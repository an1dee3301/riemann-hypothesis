module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Init.ByCases
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Instances
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.HermLocDualBasis
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))

abbrev locS : Submonoid (𝓞 E) := Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl

theorem locS_le : locS F E v ≤ nonZeroDivisors (𝓞 E) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

abbrev locR : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E (locS F E v) (locS_le F E v)

instance : IsDedekindDomain (locR F E v) :=
  IsLocalization.isDedekindDomain (𝓞 E) (locS_le F E v) _

instance : IsPrincipalIdealRing (locR F E v) :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot

omit [NumberField F] in
theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    form σ J (a • x) y = a * form σ J x y := by
  simp [form, smul_dotProduct]

omit [NumberField F] in
theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    form σ J x (a • y) = σ a * form σ J x y := by
  have : (fun i => σ ((a • y) i)) = σ a • (fun i => σ (y i)) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

omit [NumberField F] in
theorem form_sum_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E)
    (c : Fin n → E) (b : Fin n → Fin n → E) :
    form σ J y (∑ l, c l • b l) = ∑ l, σ (c l) * form σ J y (b l) := by
  have : (fun i => σ ((∑ l, c l • b l) i)) = ∑ l, σ (c l) • (fun i => σ (b l i)) := by
    ext i; simp [Finset.sum_apply, map_sum]
  simp only [form, this, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

omit [NumberField F] in
theorem form_rows (σ : E →ₐ[F] E) {n : ℕ} (J P Q : Matrix (Fin n) (Fin n) E) (k l : Fin n) :
    form σ J (P k) (Q l) = (P * J * (Q.map σ)ᵀ) k l := by
  simp only [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

theorem exists_basis (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    ∃ (t : 𝓞 F), t ∉ v.asIdeal ∧ ∃ b : Fin n → Fin n → E, LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (algebraMap (𝓞 F) (𝓞 E) t) • w ∈ Submodule.span (𝓞 E) (Set.range b) := by
  letI := hL
  obtain ⟨s, b, hb, hbL, hs⟩ := GlobalTheory.PlaceInt.LocBasis.exists_basis_up_to (A := locR F E v) (locS F E v) L (Submodule.IsLattice.fg E L)
    Submodule.IsFullLattice.span_eq_top
  obtain ⟨t, ht, hst⟩ := s.2
  exact ⟨t, ht, b, hb, hbL, fun w hw => by rw [hst]; exact hs w hw⟩

end GlobalTheory.HermLocDualBasis


open GlobalTheory.HermLocDualBasis in
theorem GlobalTheory.HermLocDualBasis.exists_locDualBasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n r s : ℕ} (X : Spc F E n), X.IsHerm σ B r s → ∀ v : Pl (F := F),
    ∃ f p : Fin n → Fin n → E, (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • f k ∈ X.L) ∧
      (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • p k ∈ X.L) ∧
      ∀ k l, form σ X.J (p k) (f l) = if k = l then 1 else 0 := by
  intro F E _ _ _ _ _ σ B n r s X hX v
  obtain ⟨t, ht, b, hb, hbL, hspan⟩ := exists_basis F E v n X.L hX.lat
  let Bm : Matrix (Fin n) (Fin n) E := Matrix.of b
  have hBm : IsUnit Bm := Matrix.linearIndependent_rows_iff_isUnit.1 hb
  let G : Matrix (Fin n) (Fin n) E := Bm * X.J * (Bm.map σ)ᵀ
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    have h1 : (Bm.map σ).det = σ Bm.det := ((σ : E →+* E).map_det Bm).symm
    have h2 : Bm.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det Bm).1 hBm |>.ne_zero
    simp only [G, Matrix.det_mul, Matrix.det_transpose, h1]
    exact mul_ne_zero (mul_ne_zero h2 (GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX))
      ((map_ne_zero σ).2 h2)
  let P : Matrix (Fin n) (Fin n) E := G⁻¹ * Bm
  have hdual : ∀ k l, form σ X.J (P k) (b l) = if k = l then 1 else 0 := by
    intro k l
    refine (form_rows F E σ X.J P Bm k l).trans ?_
    have : P * X.J * (Bm.map σ)ᵀ = 1 := by
      have e : P * X.J * (Bm.map σ)ᵀ = G⁻¹ * G := by simp only [P, G, Matrix.mul_assoc]
      rw [e]
      exact Matrix.nonsing_inv_mul G hG
    rw [this, Matrix.one_apply]
  refine ⟨b, fun k => P k, fun k => ⟨1, fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hbL k⟩,
    fun k => ⟨t, ht, ?_⟩, hdual⟩
  rw [hX.dual]
  intro x hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspan x hx)
  have hc' : ∑ l, (c l : E) • b l = algebraMap F E (t : F) • x := by
    have e1 : ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) = algebraMap F E (t : F) := rfl
    rw [← e1]
    exact hc
  rw [form_smul_left, ← AlgHom.commutes σ, ← form_smul_right, ← hc', form_sum_right]
  simp only [hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (c k).2.map (σ.toRingHom.toIntAlgHom)

end
