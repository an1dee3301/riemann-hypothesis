module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LinIndepOneDelta
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

variable {D : D7}

theorem sig_sig (D : D7) (e : D.host.E) : D.sp.cm.sig (D.sp.cm.sig e) = e := star_star e

theorem sig_fix (D : D7) (e : D.host.E) : D.sp.cm.sig e = e ↔ e ∈ (algebraMap D.host.F D.host.E).range :=
  D.sp.cm.fixed e

theorem exists_delta_D (D : D7) : ∃ δ : D.host.E, D.sp.cm.sig δ = -δ ∧ δ ≠ 0 :=
  exists_delta D.sp.cm.sig (sig_sig D) (sig_fix D) D.sp.cm.deg2

theorem exists_Delta (D : D7) (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) :
    ∃ Δ : D.host.F, algebraMap D.host.F D.host.E Δ = δ * δ := by
  have : D.sp.cm.sig (δ * δ) = δ * δ := by rw [map_mul, hδ, neg_mul_neg]
  obtain ⟨Δ, hΔ⟩ := (sig_fix D _).1 this
  exact ⟨Δ, hΔ⟩

theorem isModTop (D : D7) : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

section Pts

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

abbrev pt (a b : AF D.host.F) : AE D := mkE (F := D.host.F) δ (AF D.host.F) a b

abbrev DA (Δ : D.host.F) : AF D.host.F := algebraMap D.host.F (AF D.host.F) Δ


include hΔ in
theorem pt_mul (a b a' b' : AF D.host.F) :
    pt δ a b * pt δ a' b' = pt δ (a * a' + DA Δ * (b * b')) (a * b' + b * a') :=
  mkE_mul δ Δ hΔ (AF D.host.F) a b a' b'


theorem pt_one : pt (D := D) δ 1 0 = 1 := mkE_one δ (AF D.host.F)

abbrev coA : AE D →ₗ[AF D.host.F] AF D.host.F := cP D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)
abbrev coB : AE D →ₗ[AF D.host.F] AF D.host.F := cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)

theorem pt_co (x : AE D) : pt δ (coA δ hδ hδ0 x) (coB δ hδ hδ0 x) = x :=
  mkE_cP_cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) x

include hδ hδ0 in
theorem pt_inj {a b a' b' : AF D.host.F} (h : pt (D := D) δ a b = pt δ a' b') : a = a' ∧ b = b' :=
  mkE_inj D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) h

theorem pt_eq_smul (a b : AF D.host.F) :
    pt (D := D) δ a b = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) + b • ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ) := by
  simp only [pt, mkE, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem continuous_pt : Continuous fun p : AF D.host.F × AF D.host.F => pt (D := D) δ p.1 p.2 := by
  have := isModTop D
  have hA : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hS : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  simp only [pt_eq_smul]
  exact ((continuous_fst (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))))).add
    ((continuous_snd (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ))))

end Pts

section Unit

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)




theorem incA_eq_pt (α β : D.host.F) :
    incA D (algebraMap D.host.F D.host.E α + algebraMap D.host.F D.host.E β * δ) =
      pt δ (algebraMap D.host.F (AF D.host.F) α) (algebraMap D.host.F (AF D.host.F) β) :=
  incl_eq_mkE δ (AF D.host.F) α β

end Unit

end Formalism.IndefR.Fin.U1

end
