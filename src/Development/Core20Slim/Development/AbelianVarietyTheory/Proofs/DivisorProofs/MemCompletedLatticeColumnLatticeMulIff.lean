module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatMulAd

variable {D : D7}

theorem mulVec_map_mem_hatL {n : ℕ} (g : Matrix (Fin n) (Fin n) D.host.E)
    (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hg : ∀ x ∈ Λ, g *ᵥ x ∈ Λ') (y : Fin n → EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    g.map (eToEAf D) *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨g *ᵥ x, hg x hx, ?_⟩
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have : g.map (eToEAf D) *ᵥ (r • a) = r • (g.map (eToEAf D) *ᵥ a) := by
      show _ = (r : EAf D) • (g.map (eToEAf D) *ᵥ a)
      rw [← Matrix.mulVec_smul]
      rfl
    rw [this]; exact Submodule.smul_mem _ r ha

theorem mem_hatL_colLat_mul (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E) : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  intro v
  have h1 : ∀ x ∈ colLat B, (γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat (γ * B) := by
    intro x hx
    rw [colLat_mul]
    exact ⟨x, hx, rfl⟩
  have h2 : ∀ x ∈ colLat (γ * B), ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat B := by
    intro x hx
    rw [colLat_mul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ y) ∈ _
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy
  constructor
  · intro hv
    exact mulVec_map_mem_hatL _ _ _ h2 v hv
  · intro hv
    have := mulVec_map_mem_hatL _ _ _ h1 _ hv
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec] at this

end GlobalTheory.LatMulAd
