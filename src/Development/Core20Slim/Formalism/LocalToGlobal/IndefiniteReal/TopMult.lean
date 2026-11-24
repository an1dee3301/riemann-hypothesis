module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.TopMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adelic

variable {D : D7} {V : HSp D}

theorem mem_GfC' (h : GA D V) : h ∈ GfC V ↔ (Eqv.matA D V h).map (infPart D) = 1 := by
  show (infHom V) h = 1 ↔ _
  rw [Units.ext_iff]
  exact Iff.rfl

theorem psiT_of_mem_GfC' {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) : (Eqv.matA D V h).map (Eqv.psiT D τ) = 1 := by
  have h1 := (mem_GfC' h).1 hh
  unfold Eqv.psiT
  rw [RingHom.coe_comp, ← Matrix.map_map, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inf_GinfC_GfC' : GinfC V ⊓ GfC V = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨ha, hb⟩
  rw [Subgroup.mem_bot]
  apply Eqv.matA_inj D V
  rw [Eqv.matA_one]
  apply Eqv.mat_ext D
  · intro τ
    rw [psiT_of_mem_GfC' hb τ, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [(Eqv.mem_GinfC D V a).1 ha, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_GfC_of_psiT {h : GA D V} (hh : ∀ τ, (Eqv.matA D V h).map (Eqv.psiT D τ) = 1) : h ∈ GfC V := by
  rw [mem_GfC']
  ext i j
  rw [Matrix.map_apply]
  apply (Eqv.splitEquiv D).injective
  funext τ
  have e := congrFun (congrFun (hh τ) i) j
  rw [Matrix.map_apply] at e
  rw [Eqv.splitEquiv_apply, Eqv.splitEquiv_apply]
  change Eqv.psiT D τ (Eqv.matA D V h i j) = _
  rw [e]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem ga_decomp (g : GA D V) : ∃ h ∈ GfC V, ∃ a ∈ GinfC V, g = h * a := by
  refine ⟨g * (Eqv.infOnly D V g)⁻¹, mem_GfC_of_psiT fun τ => ?_, Eqv.infOnly D V g, Eqv.infOnly_mem_GinfC D V g,
    (inv_mul_cancel_right g _).symm⟩
  have h1 : (Eqv.matA D V g).map (Eqv.psiT D τ) = (Eqv.matA D V (Eqv.infOnly D V g)).map (Eqv.psiT D τ) := by
    rw [← Eqv.infMat_thetaC, ← Eqv.infMat_thetaC, Eqv.infMat_infOnly]
  rw [Eqv.matA_mul, Matrix.map_mul, h1, ← Matrix.map_mul, ← Eqv.matA_mul, mul_inv_cancel, Eqv.matA_one,
    Matrix.map_one _ (map_zero _) (map_one _)]


end Adelic

section GenAd

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}

end GenAd

section GenHom

variable {G H : Type} [Group G] [Group H] (f : G →* H)

end GenHom

section Generic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) (c : CoefA V)
  (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)

theorem rr_of_GinfC {a : GA D V} (ha : a ∈ GinfC V) : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.mp ha)


variable {θ M c pr}

variable {J' : Subgroup (Bridge.Gf V)} {χ' : J' →* ℂˣ} {F : Bridge.Gf V → c.W}






theorem exists_lift (y : Bridge.Gf V) : ∃ h, h ∈ GfC V ∧ (finHom V).rangeRestrict h = y := by
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective y
  obtain ⟨h, hh, a, ha, rfl⟩ := ga_decomp g
  exact ⟨h, hh, by rw [map_mul, rr_of_GinfC ha, mul_one]⟩

theorem lift_unique {h h' : GA D V} (hh : h ∈ GfC V) (hh' : h' ∈ GfC V)
    (e : (finHom V).rangeRestrict h = (finHom V).rangeRestrict h') : h = h' := by
  have h1 : h⁻¹ * h' ∈ GinfC V := by
    show h⁻¹ * h' ∈ (finHom V).ker
    have e2 := congrArg Subtype.val e
    simp only [MonoidHom.coe_rangeRestrict] at e2
    rw [MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]
  have h2 : h⁻¹ * h' ∈ GfC V := mul_mem (inv_mem hh) hh'
  have h3 : h⁻¹ * h' ∈ GinfC V ⊓ GfC V := ⟨h1, h2⟩
  rw [inf_GinfC_GfC', Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp h3



end Generic

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end Real

end Formalism.IndefR.TopMult
