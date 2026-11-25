module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

theorem ker_le_of_latIdx_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q hU n n' x y hN hidx u hu hyu
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSx
  set Sy := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (y *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSy
  let h : (Fin n' → L) ⧸ intVec L n' → (Fin n' → L) ⧸ intVec L n' := fun c =>
    if hc : ∃ u : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = c
    then QuotientAddGroup.mk (y *ᵥ (hc.choose : Fin n → L)) else 0
  have key : ∀ w : intVec L n, h (QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))) =
      (QuotientAddGroup.mk (y *ᵥ (w : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') := by
    intro w
    have hc : ∃ u' : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u' : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') =
        QuotientAddGroup.mk (x *ᵥ (w : Fin n → L)) := ⟨w, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he
    rw [QuotientAddGroup.eq]
    have hd := hN ((w : Fin n → L) - (u' : Fin n → L)) (fun i => Subring.sub_mem _ (w.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  have himg : h '' Sx = Sy := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (key w).symm⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, key w⟩
  have hcard : (h '' Sx).ncard = Sx.ncard := by
    rw [himg]
    unfold latIdx at hidx
    rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hidx
    exact hidx
  have hinj : Set.InjOn h Sx := (Set.ncard_image_iff hfin).1 hcard
  let u0 : intVec L n := ⟨u, hu⟩
  have h0 : h (QuotientAddGroup.mk (x *ᵥ ((u0 : intVec L n) : Fin n → L))) = h (QuotientAddGroup.mk (x *ᵥ ((0 : intVec L n) : Fin n → L))) := by
    rw [key, key]
    simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero]
    exact (QuotientAddGroup.eq_zero_iff _).2 hyu
  have h1 := hinj ⟨u0, rfl⟩ ⟨0, rfl⟩ h0
  simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero] at h1
  exact (QuotientAddGroup.eq_zero_iff _).1 h1

end GlobalTheory.Hk3.HoweDuality

end
