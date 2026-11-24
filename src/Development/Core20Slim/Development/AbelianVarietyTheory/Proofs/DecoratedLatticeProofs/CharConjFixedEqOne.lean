module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Tactic.Abel

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharConjFixed

theorem nontrivial_AF (D : D7) : Nontrivial (AF D.host.F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem finrank_AE (D : D7) : Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI := nontrivial_AF D
  rw [Module.finrank_baseChange]; exact D.sp.cm.deg2

theorem cA_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl


set_option synthInstance.maxHeartbeats 200000 in
theorem trace_mem (D : D7) (y : AE D) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y + cA D y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), hu, hv, map_add (f := _)]; abel
  | tmul a e =>
    have hfix : star (e + star e) = e + star e := by
      rw [star_add, star_star, add_comm]
    obtain ⟨f, hf⟩ := (D.sp.cm.fixed _).1 hfix
    refine ⟨f • a, ?_⟩
    rw [cA_tmul, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one (A := D.host.E) f,
      ← TensorProduct.smul_tmul]
    rfl

theorem fixed_mem (D : D7) (y : AE D) (hy : cA D y = y) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y := by
  obtain ⟨b, hb⟩ := trace_mem D y
  refine ⟨algebraMap D.host.F (AF D.host.F) (2⁻¹) * b, ?_⟩
  have h2 : algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (2⁻¹)) * 2 = 1 := by
    rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) 2) by rw [map_ofNat, map_ofNat],
      ← map_mul, ← map_mul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), map_one, map_one]
  rw [map_mul, hb, hy, ← two_mul, ← mul_assoc, h2, one_mul]

theorem norm_scalar (D : D7) (b : AF D.host.F) :
    Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) b) = b ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_AE]

theorem fixed_unit (D : D7) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    ∃ a : (AF D.host.F)ˣ, idF D a = x := by
  obtain ⟨b, hb⟩ := fixed_mem D x hx
  have hn : IsUnit (Algebra.norm (AF D.host.F) (x : AE D)) := x.isUnit.map _
  rw [← hb, norm_scalar] at hn
  obtain ⟨a, ha⟩ := (isUnit_pow_iff two_ne_zero).1 hn
  refine ⟨a, Units.ext ?_⟩
  rw [← hb, ← ha]; rfl

end GlobalTheory.CharConjFixed


