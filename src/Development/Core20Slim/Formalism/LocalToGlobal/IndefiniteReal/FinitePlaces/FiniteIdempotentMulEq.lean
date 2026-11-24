module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatAnn
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharStd
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import ReciprocityTheory.AdeleApproximation.AdeleIntA

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def incInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem inf_mul (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * z = incInf D (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    show _ = incInf D (fstA D.host.F a ⊗ₜ[D.host.F] e)
    have : pairA D.host.F 1 0 * a = (fstA D.host.F a, (0 : Af D.host.F)) :=
      Prod.ext (by show (1 : Ainf D.host.F) * a.1 = a.1; rw [one_mul]) (by show (0 : Af D.host.F) * a.2 = 0; rw [zero_mul])
    rw [this]; rfl
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem finite_idempotent_mul_eq (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * z = jF D (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, finPart_tmul, jF_tmul]
    congr 1
    exact Prod.ext (by show (0 : Ainf D.host.F) * a.1 = 0; rw [zero_mul]) (by show (1 : Af D.host.F) * a.2 = a.2; rw [one_mul])
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem eq_jF_of_inf (z : AE D) (hz : infPart D z = 0) : z = jF D (finPart D z) := by
  have h1 : pairA D.host.F 1 0 + pairA D.host.F 0 1 = (1 : AF D.host.F) := Prod.ext (add_zero _) (zero_add _)
  calc z = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0 + pairA D.host.F 0 1) * z := by rw [h1, map_one, one_mul]
    _ = jF D (finPart D z) := by rw [map_add (f := _), add_mul, inf_mul, hz, map_zero, zero_add, finite_idempotent_mul_eq]

theorem finPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (jF D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [jF_tmul, finPart_tmul]; rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (jF D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    rw [jF_tmul]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 a ⊗ₜ[D.host.F] e) = 0
    rw [Algebra.TensorProduct.map_tmul]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    rw [TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem approx_Af (a : Af D.host.F) (N : ℕ) (hN : 0 < N) :
    ∃ f : D.host.F, ∃ c ∈ intAf D.host.F, a = algebraMap D.host.F (Af D.host.F) f + algebraMap D.host.F (Af D.host.F) N * c := by
  have hNF : (N : D.host.F) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨u, hu⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx_adele (R := 𝓞 D.host.F)
    (algebraMap D.host.F (Af D.host.F) (1 / (N : D.host.F)) * a)
  refine ⟨N * u, _, intAf_of_isInt _ hu, ?_⟩
  rw [mul_sub, ← mul_assoc, ← map_mul, mul_one_div_cancel hNF, map_one, one_mul, ← map_mul]
  ring

theorem isAlg_Z (e : D.host.E) : IsAlgebraic ℤ e :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic e)


set_option maxHeartbeats 1600000 in
theorem approx_AfE (N : ℕ) (hN : 0 < N) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : D.host.E, ∃ y ∈ intAE D, z = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by rw [TensorProduct.tmul_zero, smul_zero, add_zero]⟩
  | tmul a e =>
    obtain ⟨m, hm0, hmint⟩ := IsAlgebraic.exists_integral_multiple (isAlg_Z e)
    have hmF : ((m : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hm0
    let e' : 𝓞 D.host.E := ⟨m • e, hmint⟩
    have he : e = (1 / (m : D.host.F)) • (e' : D.host.E) := by
      show e = (1 / (m : D.host.F)) • (m • e)
      rw [zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap D.host.F D.host.E), ← map_mul,
        one_div_mul_cancel hmF, map_one, one_mul]
    obtain ⟨f, c, hc, hfc⟩ := approx_Af ((1 / (m : D.host.F)) • a) N hN
    refine ⟨f • (e' : D.host.E), c ⊗ₜ[D.host.F] (e' : D.host.E), AddSubgroup.subset_closure ⟨c, hc, e', rfl⟩, ?_⟩
    have hN' : algebraMap D.host.F (Af D.host.F) (N : D.host.F) * c = N • c := by
      rw [map_natCast, nsmul_eq_mul]
    rw [he, ← TensorProduct.smul_tmul, hfc, TensorProduct.add_tmul, hN', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨w, y1, hy1, rfl⟩ := hx
    obtain ⟨w', y2, hy2, rfl⟩ := hy
    exact ⟨w + w', y1 + y2, add_mem hy1 hy2, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end Formalism.IndefR.Fin

end
