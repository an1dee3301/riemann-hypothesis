module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000

namespace GlobalTheory.LatVacBdd

theorem exists_ne_zero_mul_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (S : Finset (v.adicCompletion F)) :
    ∃ c : v.adicCompletion F, c ≠ 0 ∧ ∀ a ∈ S, c * a ∈ v.adicCompletionIntegers F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert b S hb ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    by_cases hcb : c * b ∈ v.adicCompletionIntegers F
    · refine ⟨c, hc0, ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hcb
      · exact hc a ha
    · have hinv : (c * b)⁻¹ ∈ v.adicCompletionIntegers F :=
        ((v.adicCompletionIntegers F).mem_or_inv_mem (c * b)).resolve_left hcb
      have hcb0 : c * b ≠ 0 := fun h => hcb (h ▸ zero_mem _)
      refine ⟨c * (c * b)⁻¹, mul_ne_zero hc0 (inv_ne_zero hcb0), ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [mul_assoc, mul_comm _ a, ← mul_assoc, mul_inv_cancel₀ hcb0]; exact one_mem _
      · rw [mul_comm c, mul_assoc]; exact mul_mem hinv (hc a ha)

end GlobalTheory.LatVacBdd

theorem GlobalTheory.LatVacBdd.locCo_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v
  classical
  choose yf zf hyz using hT.geo.hM.rat
  obtain ⟨sX, hsX⟩ := hT.geo.hV.lat.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hT.geo.hW.lat.fg.restrictScalars (R := ℤ)
  let f : (Fin a → E) →ₗ[ℤ] (Fin (a + a') → E) →ₗ[ℤ] Matrix (Fin a) (Fin (a + a')) E :=
    LinearMap.mk₂ ℤ (fun x y => Matrix.vecMulVec x y)
      (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
      (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])
  let T₀ : Finset (Matrix (Fin a) (Fin (a + a')) E) := Finset.image₂ (fun x y => f x y) sX sY
  have hmem : ∀ x ∈ G.V.L, ∀ y ∈ G.W.L, Matrix.vecMulVec x y ∈ Submodule.span ℤ (T₀ : Set _) := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin a → E)) := by
      rw [hsX]; exact hx
    have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin (a + a') → E)) := by
      rw [hsY]; exact hy
    have := Submodule.apply_mem_map₂ f hx' hy'
    rw [Submodule.map₂_span_span] at this
    rw [Finset.coe_image₂]; exact this
  have hgen : latAtV G.V G.W v ≤ AddSubgroup.closure {z | ∃ b : AF F,
      At (evFin F v) b ∧ evFin F v b ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = b • incM F t} := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨b, hb, hbv, x, hx, y, hy, rfl⟩
    let g : Matrix (Fin a) (Fin (a + a')) E →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
      (DistribSMul.toAddMonoidHom _ b).comp
        (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom)
    have h1 : Matrix.vecMulVec x y ∈ AddSubgroup.closure (T₀ : Set _) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hmem x hx y hy
    have h2 : g (Matrix.vecMulVec x y) ∈ (AddSubgroup.closure (T₀ : Set _)).map g :=
      AddSubgroup.mem_map_of_mem g h1
    rw [AddMonoidHom.map_closure] at h2
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨b, hb, hbv, t, ht, rfl⟩
  let S : Finset (Fv F v) :=
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (yf p.1 p.2)) ∪
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (zf p.1 p.2))
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatVacBdd.exists_ne_zero_mul_mem v S
  have hcy : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hcz : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hev : ∀ y : F, evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := fun y => AlgHom.commutes _ _
  refine ⟨c, hc0, fun γ hγ => ?_⟩
  clear_value T₀
  revert hγ
  intro hγ
  have hγ' := hgen hγ
  clear hγ
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, -, hbv, t, ht, rfl⟩ := hz
    intro k
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, hyz,
      Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, hev]
    exact ⟨by rw [mul_left_comm]; exact mul_mem hbv (hcy t ht k),
      by rw [mul_left_comm]; exact mul_mem hbv (hcz t ht k)⟩
  | zero => intro k; simp
  | add x y _ _ hx hy =>
    intro k
    rw [map_add (f := _)]
    exact ⟨by rw [Prod.fst_add, Pi.add_apply, mul_add]; exact add_mem (hx k).1 (hy k).1,
      by rw [Prod.snd_add, Pi.add_apply, mul_add]; exact add_mem (hx k).2 (hy k).2⟩
  | neg x _ hx =>
    intro k
    rw [map_neg]
    exact ⟨by rw [Prod.fst_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).1,
      by rw [Prod.snd_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).2⟩
