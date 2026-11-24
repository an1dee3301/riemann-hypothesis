module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisExtra
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.InclEIntMem
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.RingTheory.FiniteType

@[expose] public section

noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.MainNotions.S Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.AutInhab

section Cong

variable {A : Type} [CommRing A] {S : Subring A} {n : Type} [Fintype n] [DecidableEq n]

theorem natCast_smul_mem (Λ : Submodule S (n → A)) (m : ℕ) {y : n → A} (hy : y ∈ Λ) : (m : A) • y ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy m

def congSub (Λ : Submodule S (n → A)) (g : ℕ) : Subgroup (GL n A) where
  carrier := {x | x ∈ stabGL Λ ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ((x : Matrix n n A) - 1) *ᵥ y = (g : A) • z}
  one_mem' := ⟨one_mem _, fun y _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := ha' _ ((hb y).1 hy)
    obtain ⟨z', hz', e'⟩ := hb' y hy
    refine ⟨z + z', add_mem hz hz', ?_⟩
    rw [smul_add, ← e, ← e', Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
    congr 1
    rw [Units.val_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := ha' _ (((stabGL Λ).inv_mem ha y).1 hy)
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [smul_neg, ← e, Matrix.mulVec_mulVec, ← Matrix.neg_mulVec]
    congr 1
    rw [Matrix.sub_mul, Matrix.one_mul, Units.mul_inv]; abel

theorem congSub_mul_le (Λ : Submodule S (n → A)) (g h : ℕ) : congSub Λ (g * h) ≤ congSub Λ g := by
  rintro x ⟨hx, hx'⟩
  refine ⟨hx, fun y hy => ?_⟩
  obtain ⟨z, hz, e⟩ := hx' y hy
  exact ⟨(h : A) • z, natCast_smul_mem Λ h hz, by rw [e, smul_smul, Nat.cast_mul]⟩

theorem conj_mem_congSub (Λ : Submodule S (n → A)) (x : GL n A) {M N : ℕ} (hN : IsUnit (N : A))
    (hx : ∀ y ∈ Λ, (M : A) • (x : Matrix n n A) *ᵥ y ∈ Λ)
    (hx' : ∀ y ∈ Λ, (N : A) • ((x⁻¹ : GL n A) : Matrix n n A) *ᵥ y ∈ Λ) (g : ℕ)
    {k : GL n A} (hk : k ∈ congSub Λ (N * (g * M))) : x * k * x⁻¹ ∈ congSub Λ g := by
  have key : ∀ k ∈ congSub Λ (N * (g * M)), ∀ y ∈ Λ, ∃ z ∈ Λ,
      (((x * k * x⁻¹ : GL n A) : Matrix n n A) - 1) *ᵥ y = (g : A) • z := by
    rintro k ⟨-, hk⟩ y hy
    obtain ⟨z, hz, e⟩ := hk _ (hx' y hy)
    refine ⟨_, hx z hz, ?_⟩
    rw [Matrix.mulVec_smul, Nat.cast_mul, mul_smul, hN.smul_left_cancel] at e
    have e1 : ((x * k * x⁻¹ : GL n A) : Matrix n n A) - 1 =
        (x : Matrix n n A) * (((k : Matrix n n A) - 1) * ((x⁻¹ : GL n A) : Matrix n n A)) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Units.mul_inv, Units.val_mul, Units.val_mul,
        Matrix.mul_assoc]
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, Nat.cast_mul, mul_smul]
  have into : ∀ k ∈ congSub Λ (N * (g * M)), ∀ y ∈ Λ, ((x * k * x⁻¹ : GL n A) : Matrix n n A) *ᵥ y ∈ Λ := by
    intro k hk y hy
    obtain ⟨z, hz, e⟩ := key k hk y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add] at e
    rw [e]; exact add_mem (natCast_smul_mem Λ g hz) hy
  refine ⟨fun y => ⟨into k hk y, fun h => ?_⟩, key k hk⟩
  have := into k⁻¹ (inv_mem hk) _ h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, show x * k⁻¹ * x⁻¹ * (x * k * x⁻¹) = 1 by group,
    Units.val_one, Matrix.one_mulVec] at this

theorem exists_denom (Λ : Submodule S (n → A)) (hfg : Λ.FG)
    (habs : ∀ v : n → A, ∃ N : ℕ, 1 ≤ N ∧ (N : A) • v ∈ Λ) (X : Matrix n n A) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ y ∈ Λ, (N : A) • X *ᵥ y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.SublatticeFacts.main
  | exact _root_.GlobalTheory.SublatticeFacts.main
  | (apply _root_.GlobalTheory.SublatticeFacts.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SublatticeFacts.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SublatticeFacts.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SublatticeFacts.main ..)

@[reducible] def congBasis (Λ : Submodule S (n → A)) (hfg : Λ.FG)
    (habs : ∀ v : n → A, ∃ N : ℕ, 1 ≤ N ∧ (N : A) • v ∈ Λ) (hu : ∀ N : ℕ, 1 ≤ N → IsUnit (N : A))
    (H : Subgroup (GL n A)) : GroupFilterBasis H where
  sets := {U | ∃ g : ℕ, 1 ≤ g ∧ U = ((congSub Λ g).subgroupOf H : Set H)}
  nonempty := ⟨_, 1, le_rfl, rfl⟩
  inter_sets := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    refine ⟨_, ⟨g * h, Nat.mul_pos hg hh, rfl⟩, fun x hx => ⟨congSub_mul_le Λ g h hx, ?_⟩⟩
    rw [mul_comm] at hx
    exact congSub_mul_le Λ h g hx
  one' := by
    rintro _ ⟨g, -, rfl⟩
    exact one_mem _
  mul' := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem ha hb
  inv' := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, fun a ha => inv_mem ha⟩
  conj' := by
    rintro x _ ⟨g, hg, rfl⟩
    obtain ⟨M, hM, hx⟩ := exists_denom Λ hfg habs ((x : GL n A) : Matrix n n A)
    obtain ⟨N, hN, hx'⟩ := exists_denom Λ hfg habs (((x : GL n A)⁻¹ : GL n A) : Matrix n n A)
    exact ⟨_, ⟨N * (g * M), Nat.mul_pos hN (Nat.mul_pos hg hM), rfl⟩,
      fun k hk => conj_mem_congSub Λ (x : GL n A) (hu N hN) hx hx' g hk⟩

end Cong

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem isUnit_natCast (N : ℕ) (hN : 1 ≤ N) : IsUnit (N : E ⊗[F] Af F) := by
  have : IsUnit (N : E) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))
  simpa using this.map (inclE (F := F) (Af F))

theorem lamAf_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) : (lamAf (F := F) L).FG := by
  first
  | exact @_root_.GlobalTheory.VectorInclusion.main
  | exact _root_.GlobalTheory.VectorInclusion.main
  | (apply _root_.GlobalTheory.VectorInclusion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.VectorInclusion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.VectorInclusion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.VectorInclusion.main ..)

theorem exists_nat_multiple (d : 𝓞 F) (hd : d ≠ 0) : ∃ N : ℕ, 1 ≤ N ∧ ∃ d' : 𝓞 F, d' * d = N := by
  have h := Ideal.absNorm_mem (Ideal.span {d})
  obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton'.1 h
  refine ⟨_, Nat.pos_of_ne_zero ?_, d', hd'⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hd

theorem levelafC_natCast (N : ℕ) : Formalism.UG.P.levelafC (F := F) E (N : 𝓞 F) = (N : E ⊗[F] Af F) := by
  rw [← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]

theorem lamAf_absorbs (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (v : Fin n → E ⊗[F] Af F) : ∃ N : ℕ, 1 ≤ N ∧ (N : E ⊗[F] Af F) • v ∈ lamAf (F := F) L := by
  classical
  obtain ⟨c, hc, h⟩ := Formalism.UG.P.adelstabL_lower (F := F) L hL
  choose d hd0 hd using fun i => Formalism.UG.P.levelaf_denom (v i)
  have hD : ∀ i, Formalism.UG.P.levelafC E (∏ j, d j) * v i ∈ IntAf F E := by
    intro i
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Formalism.UG.P.levelafC_mul, mul_assoc]
    exact mul_mem (Formalism.UG.P.levelafC_mem _) (hd i)
  obtain ⟨N, hN, d', e⟩ := exists_nat_multiple (c * ∏ j, d j)
    (mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun i _ => hd0 i))
  refine ⟨N, hN, ?_⟩
  have h1 := h (fun i => Formalism.UG.P.levelafC E d' * (Formalism.UG.P.levelafC E (∏ j, d j) * v i))
    fun i => mul_mem (Formalism.UG.P.levelafC_mem _) (hD i)
  have h2 : (N : E ⊗[F] Af F) • v = fun i => Formalism.UG.P.levelafC E c *
      (Formalism.UG.P.levelafC E d' * (Formalism.UG.P.levelafC E (∏ j, d j) * v i)) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← levelafC_natCast, ← e, Formalism.UG.P.levelafC_mul, Formalism.UG.P.levelafC_mul]
    ring
  rw [h2]
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[reducible] def adelicBasis (L : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hL : L.FG)
    (H : Subgroup (GL (Fin n) (E ⊗[F] Af F))) : GroupFilterBasis H :=
  congBasis (lamAf (F := F) L) (lamAf_fg L hL) (lamAf_absorbs L hs) isUnit_natCast H

end Adelic

section Real

variable {n : ℕ}

def signEquiv (ε : Fin n → Bool) :
    Fin (Finset.univ.filter fun a => ε a = true).card ⊕ Fin (Finset.univ.filter fun a => ε a = false).card ≃ Fin n :=
  (Equiv.sumCongr
    (Fintype.equivFinOfCardEq (Fintype.card_subtype fun a => ε a = true)).symm
    (Fintype.equivFinOfCardEq (α := {a // ¬ ε a = true}) (by rw [Fintype.card_subtype]; simp)).symm).trans
    (Equiv.sumCompl fun a => ε a = true)

theorem Jm_submatrix (ε : Fin n → Bool) :
    (Formalism.REAL.Jm ε).submatrix (signEquiv ε) (signEquiv ε) = Jpq _ _ := by
  have h1 : ∀ a, ε (signEquiv ε (Sum.inl a)) = true := fun a =>
    ((Fintype.equivFinOfCardEq (Fintype.card_subtype fun a => ε a = true)).symm a).2
  have h2 : ∀ a, ¬ ε (signEquiv ε (Sum.inr a)) = true := fun a =>
    ((Fintype.equivFinOfCardEq (α := {a // ¬ ε a = true}) (by rw [Fintype.card_subtype]; simp)).symm a).2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.REAL.Jm, Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2]
  split_ifs <;> simp

theorem hasSignature_of_frame {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * G * P = Formalism.REAL.Jm ε) :
    HasSignature G (Finset.univ.filter fun a => ε a = true).card
      (Finset.univ.filter fun a => ε a = false).card := by
  set e := signEquiv ε
  have hQ : IsUnit (P.submatrix e e) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det P).1 hP
  refine ⟨e.symm, hQ.unit, ?_⟩
  rw [Formalism.UG.P.cT_conj_eq, IsUnit.unit_spec, ← Jm_submatrix, ← h, Matrix.reindex_apply, Equiv.symm_symm,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem exists_frame_of_hasSignature {G : Matrix (Fin n) (Fin n) ℂ} (ε : Fin n → Bool)
    (h : HasSignature G (Finset.univ.filter fun a => ε a = true).card
      (Finset.univ.filter fun a => ε a = false).card) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P ∧ Pᴴ * G * P = Formalism.REAL.Jm ε := by
  obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data G _ _ h
  set e := signEquiv ε
  have hP : (Q.submatrix id e.symm)ᴴ * G * Q.submatrix id e.symm = Formalism.REAL.Jm ε := by
    have : (Q.submatrix id e.symm)ᴴ * G * Q.submatrix id e.symm = (Qᴴ * G * Q).submatrix e.symm e.symm := by
      ext i j; simp [Matrix.mul_apply]
    rw [this, hQ, ← Jm_submatrix, Matrix.submatrix_submatrix]
    simp [e]
  refine ⟨_, ?_, hP⟩
  refine IsUnit.of_mul_eq_one_right (Formalism.REAL.Jm ε * ((Q.submatrix id e.symm)ᴴ * G)) ?_
  rw [Matrix.mul_assoc, hP, Formalism.REAL.Jm_mul_self]

def firstSigns (n p : ℕ) : Fin n → Bool := fun a => decide ((a : ℕ) < p)

theorem card_firstSigns_true {p q : ℕ} (h : n = p + q) :
    (Finset.univ.filter fun a => firstSigns n p a = true).card = p := by
  have : (Finset.univ.filter fun a => firstSigns n p a = true) = Finset.univ.filter fun a : Fin n => (a : ℕ) < p := by
    ext a; simp [firstSigns]
  rw [this, Fin.card_filter_val_lt]
  omega

theorem card_firstSigns_false {p q : ℕ} (h : n = p + q) :
    (Finset.univ.filter fun a => firstSigns n p a = false).card = q := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a => firstSigns n p a = true)
  rw [card_firstSigns_true h, Finset.card_univ, Fintype.card_fin] at h1
  simp only [Bool.not_eq_true] at h1
  omega

theorem exists_frame {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsHerm (starRingEnd ℂ) G) (hd : IsUnit G.det) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * G * P = Formalism.REAL.Jm ε := by
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ G hG hd
  have hn : n = p + q := by simpa using (Formalism.UG.P.sig_data G p q h).1
  refine ⟨firstSigns n p, exists_frame_of_hasSignature _ ?_⟩
  rwa [card_firstSigns_true hn, card_firstSigns_false hn]

end Real


section Inst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

















end Inst

end GlobalTheory.AutInhab
