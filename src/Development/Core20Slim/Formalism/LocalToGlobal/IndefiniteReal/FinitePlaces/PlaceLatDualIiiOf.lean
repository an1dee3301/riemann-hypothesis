module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualASt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartSplitIdem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
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
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev fI (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem pairA_mul_one (α : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 1 = pairA D.host.F 0 α :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (by show α * 1 = α; rw [mul_one])

theorem splitIdem_mul_fI {e' : AE D} (h : IsSplitIdem D e') : e' * fI D = e' := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, h3⟩ := h
  have he : e' = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
    rw [← h3, mul_add, h1, h2, add_zero]
  calc e' * fI D = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * fI D := by rw [← he]
    _ = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α * pairA D.host.F 0 1) := by
        rw [map_mul, mul_assoc]
    _ = e' := by rw [pairA_mul_one, ← he]

theorem splitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hv, by rw [cA_cA, add_comm, h3]⟩

theorem idemSum_mul_fI {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    e * fI D = e ∧ cA D e * fI D = cA D e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact ⟨Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (hes PP hPP).1,
    Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (splitIdem_cA (hes PP hPP).1)⟩

theorem idemSum_int {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) :
    finPart D e ∈ intAE D ∧ finPart D (cA D e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine ⟨?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (hes PP hPP).1
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, map_sum]
      exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (splitIdem_cA (hes PP hPP).1)

theorem infPart_fI : infPart D (fI D) = 0 := by
  show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 0
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem half_infPart {m n : ℕ} {f : AE D} (hf : f * fI D = f) {y : Mx D m n} (hy : IsHalf f y) :
    y.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  calc infPart D (y i j) = infPart D ((f * fI D) * y i j) := by rw [hf, hy i j]
    _ = 0 := by rw [map_mul, map_mul, infPart_fI, mul_zero, zero_mul]

variable (S T : HSp D)

theorem hO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    hO S T y u = hO S T y (f • u) := by
  unfold hO
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  conv_lhs => rw [← hy d a]
  ring

theorem symplO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    symplO S T y u = symplO S T y (f • u) := by
  unfold symplO; rw [hO_half_right S T hy u]

variable {S T}

theorem placeLatDualIi_of (hL : LatSelfDual D) : PlaceLatDualIi D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he y hy
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, hfc⟩ := idemSum_mul_fI he
  have hie := (idemSum_int he).1
  have hee := idemSum_mul_self he
  have hy0 : y.map (infPart D) = 0 := half_infPart hfc hy
  constructor
  · intro hx
    refine (hL4 y hy0).2 fun u hu => ?_
    have hm : e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hie hu
    have hh : IsHalf e (e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
    have h1 := hx _ hm hh
    rw [symplO_half_right S T hy u, symplO_swap S T (e • u) y, AddChar.map_neg_eq_inv, h1, inv_one]
  · intro hyL x hx hxh
    exact (hL4 x (half_infPart hfe hxh)).1 hx y hyL

theorem placeLatDualIii_of (hL : LatSelfDual D) : PlaceLatDualIii D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he x hx
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, -⟩ := idemSum_mul_fI he
  have hic := (idemSum_int he).2
  have hee := idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hx0 : x.map (infPart D) = 0 := half_infPart hfe hx
  have hxc : IsHalf (cA D (cA D e)) x := by rw [cA_cA]; exact hx
  constructor
  · intro hy
    refine (hL4 x hx0).2 fun u hu => ?_
    have hm : cA D e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hic hu
    have hh : IsHalf (cA D e) (cA D e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
    rw [symplO_half_right S T hxc u]
    exact hy _ hm hh
  · intro hxL y hy _
    exact (hL4 x hx0).1 hxL y hy

end Formalism.IndefR.Fin.PDA

end
