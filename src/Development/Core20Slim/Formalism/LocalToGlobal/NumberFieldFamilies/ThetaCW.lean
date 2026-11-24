module
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.Core20Slim.Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic


@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem inf_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) : θ (infPart D (x : AE D)) ≠ 0 :=
  ((x.isUnit.map (infPart D)).map θ).ne_zero

theorem hasInfExp_mul {χ χ' : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (h : HasInfExp D χ τ a)
    (h' : HasInfExp D χ' τ b) : HasInfExp D (χ * χ') τ (a + b) := by
  obtain ⟨n, hn, e⟩ := h
  obtain ⟨m, hm, e'⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, allSome_fam.2 fun x h1 h2 => ?_⟩
  have hz := inf_ne_zero (th0 D τ) x
  rw [MonoidHom.mul_apply, Circle.coe_mul, allSome_fam.1 e x h1 h2, allSome_fam.1 e' x h1 h2, zpow_add₀]
  exact div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)

theorem hasInfExp_inv {χ : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) :
    HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, e⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, allSome_fam.2 fun x h1 h2 => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, allSome_fam.1 e x h1 h2, _root_.zpow_neg]

theorem hasInfExp_one (τ : D.what₂.Tau) : HasInfExp D (1 : (AE D)ˣ →* Circle) τ 0 :=
  ⟨0, by simp, allSome_fam.2 fun x _ _ => by simp⟩


variable (D) in
def chrA : Subgroup ((AE D)ˣ →* Circle) where
  carrier := {χ | IsHeckeChar D χ ∧ ∀ τ, ∃ a, HasInfExp D χ τ a}
  one_mem' := ⟨⟨continuous_const, fun _ => rfl⟩, fun τ => ⟨0, hasInfExp_one τ⟩⟩
  mul_mem' := fun {a b} ha hb => ⟨⟨ha.1.1.mul hb.1.1, fun x => by rw [MonoidHom.mul_apply, ha.1.2, hb.1.2, one_mul]⟩,
    fun τ => by
      obtain ⟨s, hs⟩ := ha.2 τ
      obtain ⟨t, ht⟩ := hb.2 τ
      exact ⟨_, hasInfExp_mul hs ht⟩⟩
  inv_mem' := fun {a} ha => ⟨⟨ha.1.1.inv, fun x => by rw [MonoidHom.inv_apply, ha.1.2, inv_one]⟩,
    fun τ => by
      obtain ⟨s, hs⟩ := ha.2 τ
      exact ⟨_, hasInfExp_inv hs⟩⟩

def ExpU (D : D7) : Prop := ∀ (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D χ τ a → HasInfExp D χ τ b → a = b












variable {ψ : AddChar (AF D.host.F) ℂ}





end Formalism.L2.Fam.ThC

end
