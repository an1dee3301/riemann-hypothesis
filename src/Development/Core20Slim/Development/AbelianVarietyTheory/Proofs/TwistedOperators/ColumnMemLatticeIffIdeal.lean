module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitaryEmbeddingColumns

open GlobalTheory.FinPl GlobalTheory.SeeSaw


theorem incA_mul_tmul' {D : D7} (e : D.host.E) (y : AF D.host.F) (z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA {D : D7} (y : AF D.host.F) (t e : D.host.E) :
    (y ⊗ₜ[D.host.F] t) * incA D e = y ⊗ₜ[D.host.F] (t * e) := by
  show (y ⊗ₜ[D.host.F] t) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]




set_option maxHeartbeats 1000000 in
theorem mem_of_mem_idV {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v) : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) := by
  classical
  let Ψ : AE D →+ (Fin B.rank → AE D) := AddMonoidHom.pi fun k => AddMonoidHom.mulRight (incA D (d.a k q))
  have hle : idV (𝔟 q) v ≤ (latV B (d.lat Λ 𝔟) (· = v)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, t, ht, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hαv, 1, Set.mem_singleton _, d.a *ᵥ Pi.single q t, ?_, ?_⟩
    · refine ⟨0, Λ.zero_mem, Pi.single q t, fun p => ?_, by simp⟩
      by_cases hp : p = q
      · subst hp; simpa using ht
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] t) * incA D (d.a k q) = _
      rw [tmul_mul_incA, one_mul]
      congr 1
      rw [mulVec_single, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply, mul_comm]
  exact hle h


end GlobalTheory.UnitaryEmbeddingColumns

end
