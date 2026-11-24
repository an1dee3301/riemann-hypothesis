module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

variable {D : D7} {S T : HSp D}

theorem cA_incA_inv_natCast (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_natCast]

theorem symplO_inv_smul_nsmul {m : ℕ} (hm : 0 < m) (y l : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • y) (m • l) = symplO S T y l := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_inv_natCast, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem symplO_inv_smul_swap (m : ℕ) (x u : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • x) u = -symplO S T (incA D ((m : D.host.E)⁻¹) • u) x := by
  rw [GlobalTheory.PlaceModel.symplO_skew S T x (incA D ((m : D.host.E)⁻¹) • u), neg_neg, GlobalTheory.PlaceModel.symplO_smul,
    cA_incA_inv_natCast]

theorem map_infPart_smul (a : AE D) {r : WO S T} (hr : r.map (infPart D) = 0) : (a • r).map (infPart D) = 0 := by
  ext i j
  have hij := congrFun (congrFun hr i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at hij ⊢
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, hij, mul_zero]

theorem nsmul_inv_smul {m : ℕ} (hm : 0 < m) (x : WO S T) : m • (incA D ((m : D.host.E)⁻¹) • x) = x := by
  rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem psi_shift {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) {r : WO S T} (hr : r ∈ Λ) {x : WO S T} (hx : x ∈ mLat m Λ) :
    ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • x) r) = 1 := by
  obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hx
  rw [GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]
  exact hΛ l hl r hr

def qCharM (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) : AddChar (Qm m Λ) ℂ where
  toFun u := ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r)
  map_zero_eq_one' := psi_shift hm hΛ hr repm_zero_mem
  map_add_eq_mul' a b := by
    have h := psi_shift hm hΛ hr (repm_add_sub a b)
    have e : repm (a + b) = (repm (a + b) - (repm a + repm b)) + repm a + repm b := by abel
    rw [e, smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_apply (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) (u : Qm m Λ) :
    qCharM ψ Λ m hm hΛ r hr u = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r) := rfl

theorem qCharM_mk (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) {u : WO S T} (hu : u ∈ Λ) :
    qCharM ψ Λ m hm hΛ r hr (QuotientAddGroup.mk (⟨u, hu⟩ : Λ)) = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • u) r) := by
  rw [qCharM_apply]
  have h := psi_shift hm hΛ hr (repm_mk_sub (m := m) hu)
  have e : repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) =
      (repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) - u) + u := by abel
  rw [e, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_eq_zero_iff {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    {r : WO S T} (hr : r ∈ Λ) : qCharM ψ Λ m hm hΛ r hr = 0 ↔ r ∈ mLat m Λ := by
  constructor
  · intro h0
    have hx : incA D ((m : D.host.E)⁻¹) • r ∈ Λ := by
      refine hmax _ (map_infPart_smul _ (hinf r hr)) fun u hu => ?_
      have h1 := qCharM_mk ψ Λ m hm hΛ r hr hu
      rw [h0, AddChar.zero_apply] at h1
      rw [symplO_inv_smul_swap, AddChar.map_neg_eq_inv, ← h1, inv_one]
    exact mem_mLat.2 ⟨_, hx, nsmul_inv_smul hm r⟩
  · intro hrm
    obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hrm
    refine DFunLike.ext _ _ (fun u => ?_)
    rw [qCharM_apply, AddChar.zero_apply, symplO_inv_smul_nsmul hm]
    exact hΛ _ (repm_mem u) _ hl

theorem charSum_selfAnn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ), 0 < m →
    (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) →
    (∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ) →
    ∀ [Fintype (Qm m Λ)] [DecidableEq (Qm m Λ)] (q : Qm m Λ),
      ∑ u : Qm m Λ, ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) (repm q)) =
        if q = 0 then (Fintype.card (Qm m Λ) : ℂ) else 0 := by
  intro D ψ S T Λ m hm hinf hΛ hmax _ _ q
  have key : qCharM ψ Λ m hm hΛ (repm q) (repm_mem q) = 0 ↔ q = 0 := by
    rw [qCharM_eq_zero_iff hm hinf hΛ hmax (repm_mem q)]
    conv_rhs => rw [← mk_repm q]
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  classical
  have hs := AddChar.sum_eq_ite (qCharM ψ Λ m hm hΛ (repm q) (repm_mem q))
  simp only [qCharM_apply, key] at hs
  convert hs
end GlobalTheory.FinDecomp
end
