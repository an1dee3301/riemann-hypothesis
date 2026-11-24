module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementC
public import Init.Core
public import Init.Data.Int.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
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
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory   
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevRedTriv

open Formalism.L2.DIV

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem coord_mem_idS {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) (i : Fin n) :
    ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z) i := by
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 with hB
  revert i
  refine Submodule.span_induction
    (p := fun z _ => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (B *ᵥ z) i)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on
      (p := fun x => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        (B *ᵥ fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) i) hx ?_ ?_
    · intro p hp l hl i
      have hlm : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨l, hl, rfl⟩
      have ht := (hβ _).1 hlm i
      refine ⟨oToS F E p * ⟨_, ht⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp), ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((p • l) i)) =
          ((oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
        funext k
        rw [Pi.smul_apply, Pi.smul_apply, oToS_coe, smul_eq_mul]
        show ((p : E) * l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) =
          (algebraMap (𝓞 E) E p) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) * ((l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
    · intro x₁ x₂ h₁ h₂ i
      obtain ⟨s₁, hs₁, e₁⟩ := h₁ i
      obtain ⟨s₂, hs₂, e₂⟩ := h₂ i
      refine ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((x₁ + x₂) i)) =
          (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₁ i)) +
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₂ i)) := by
        funext k; simp
      rw [e, Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]
  · intro i
    exact ⟨0, Ideal.zero_mem _, by simp⟩
  · intro a c _ _ ha hc i
    obtain ⟨s₁, hs₁, e₁⟩ := ha i
    obtain ⟨s₂, hs₂, e₂⟩ := hc i
    exact ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, by rw [Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]⟩
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    have : c • a = ((c : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • a := rfl
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]

theorem coe_sub_one_apply (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((intGL F E n y).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem conj_sub_one {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (h : X = β.1 * Y * (β⁻¹).1) : Y - 1 = (β⁻¹).1 * (X - 1) * β.1 := by
  subst h
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]


theorem col_entry {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (e2 : Y - 1 = (β⁻¹).1 * (X - 1) * β.1) (c : R) (i j : Fin m) :
    ((β⁻¹).1 *ᵥ (c • ((X - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)))) i = c * (Y - 1) i j := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← e2,
    Matrix.mulVec_single_one]
  rfl

theorem redFn_eq_one_of_cols {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ St β) (b : 𝓞 E)
    (hb : b ∉ PP.asIdeal)
    (h : ∀ j, ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
      ((x.1 - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) :
    redFn β PP x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  have e2 : (intGL F E n y).1 - 1 = (β⁻¹).1 * ((frGL β y).1 - 1) * β.1 := conj_sub_one β _ _ rfl
  have hprime : PP.asIdeal.IsPrime := PP.isPrime
  have hb0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  obtain ⟨s, hs, es⟩ := coord_mem_idS hβ PP (h j) i
  rw [col_entry β _ _ e2] at es
  have es' : s = oToS F E b * (y.1 - 1) i j := by
    apply Subtype.ext
    rw [Subring.coe_mul, coe_sub_one_apply, es]
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    have h0 : resS F PP s = 0 := by
      rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff]; exact hs
    rw [es', map_mul, resS_oToS] at h0
    exact (mul_eq_zero.1 h0).resolve_left hb0
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end General

section Adelic




end Adelic

end GlobalTheory.LevRedTriv
