module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceAt
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FourVac
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceHeis
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceInst
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulSubMulLe
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem exists_invForm (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T))
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hlev : ∀ f, IsThetaFunO ψ S T f → ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ Λ, (IsHalf e₁ u ∨ IsHalf (cA D e₁) u) → heisO ψ S T (k • u) f = f)
    {w : WO S T → ℂ} (hw : IsThetaFunO ψ S T w) (hwX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u w = w)
    (hwY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u w = w) (hw0 : w ≠ 0) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e₁ * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f →
        ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ w ≠ 0 := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  let N : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ
    {v | ∃ u ∈ halfSub S T (cA D e₁), ∃ G ∈ {f : WO S T → ℂ | IsThetaFunO ψ S T f}, v = heisL ψ S T u G - G}
  have hwN : w ∉ N := by
    intro hmem
    refine hw0 (Four.vac_eq_zero_of_mem_span (ρ := heisL ψ S T) (χ := fun t y => ψ (symplO S T t y))
      (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁))
      (fun y hy y' hy' => heisL_add_half ψ S T (cA_half_orth he) hy hy')
      (fun x _ y _ => heisL_comm ψ S T x y)
      (fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
      (fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
      (fun t y => psi_ne_zero ψ _)
      (fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
      (fun y hy h => hdY y hy fun x hx hxe => h x (AddSubgroup.mem_inf.2 ⟨hx, hxe⟩))
      (fun k hk => by
        obtain ⟨R, hR⟩ := hfX k hk
        exact finite_qt_of S T R fun u hu => by
          obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
          exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
      (fun k hk => by
        obtain ⟨R, hR⟩ := hfY k hk
        exact finite_qt_of S T R fun u hu => by
          obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
          exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
      (fun k hk t h => nsmul_eq_zero_WO S T hk h)
      (fun y hy => hoY y hy) {f | IsThetaFunO ψ S T f}
      (fun G hG => by
        obtain ⟨k, hk, hGk⟩ := hlev G hG
        exact ⟨k, hk, fun u hu => hGk u (mi hu).1 (Or.inl (mi hu).2),
          fun u hu => hGk u (mi hu).1 (Or.inr (mi hu).2)⟩)
      (fun u hu => hwX u (mi hu).1 (mi hu).2) (fun u hu => hwY u (mi hu).1 (mi hu).2) hmem)
  obtain ⟨ℓ, hℓw, hℓN⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwN inferInstance
  refine ⟨ℓ, fun u hu f hf => ?_, hℓw⟩
  have hmem : heisL ψ S T u f - f ∈ N := Submodule.subset_span ⟨u, hu, f, hf, rfl⟩
  have h0 : ℓ (heisL ψ S T u f - f) = 0 := by
    have : ℓ (heisL ψ S T u f - f) ∈ N.map ℓ := Submodule.mem_map_of_mem hmem
    rw [hℓN] at this
    exact (Submodule.mem_bot ℂ).1 this
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end Formalism.IndefR.Fin

end
