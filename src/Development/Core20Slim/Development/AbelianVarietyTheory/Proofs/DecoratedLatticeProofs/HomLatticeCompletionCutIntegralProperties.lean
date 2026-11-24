module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem pairA_zero_mul_pairA_zero (F : Type) [Field F] [NumberField F] (a b : Af F) :
    pairA F 0 a * pairA F 0 b = pairA F 0 (a * b) := by
  show (((0 : Ainf F), a) * ((0 : Ainf F), b) : Ainf F × Af F) = ((0 : Ainf F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem pairA_zero_smul_tmul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : Af F) (e : E) :
    pairA F 0 a • (pairA F 0 b ⊗ₜ[F] e : AF F ⊗[F] E) = pairA F 0 (a * b) ⊗ₜ[F] e := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, pairA_zero_mul_pairA_zero]

theorem infPart_pairA_zero_tmul (D : D7) (b : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 b ⊗ₜ[D.host.F] e) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (pairA D.host.F 0 b ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  have : fstA D.host.F (pairA D.host.F 0 b) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem latO_algebra : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (u : WO S T), u ∈ latO S T LS LT P → (∀ γ ∈ intAf D.host.F, pairA D.host.F 0 γ • u ∈ latO S T LS LT (fun v => P v ∧ evalV D.host.F v γ ≠ 0)) ∧ pairA D.host.F 0 1 • u = u ∧ u.map (infPart D) = 0 ∧ ((∀ v, ¬ P v) → u = 0) := by
  intro D S T LS LT P u hu
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]
        exact mul_mem (hγ v) (hα v)
      · rw [map_mul]
        by_cases h : P v
        · have : evalV D.host.F v γ = 0 := by
            by_contra h'
            exact hv ⟨h, h'⟩
          rw [this, zero_mul]
        · rw [hP v h, mul_zero]
      · ext i j
        exact pairA_zero_smul_tmul _ _ _ _ _
    · ext i j
      have := pairA_zero_smul_tmul D.host.F D.host.E 1 α (a * t i * ∑ k, star (s k) * S.gram k j)
      rw [one_mul] at this
      exact this
    · ext i j
      exact infPart_pairA_zero_tmul D α _
    · have h0 : α = 0 := by
        apply RestrictedProduct.ext
        intro v
        exact hP v (h v)
      subst h0
      ext i j
      have : pairA D.host.F 0 0 = 0 := rfl
      show pairA D.host.F 0 0 ⊗ₜ[D.host.F] _ = (0 : AE D)
      rw [this, TensorProduct.zero_tmul]
  | zero =>
    refine ⟨fun γ _ => ?_, smul_zero _, ?_, fun _ => rfl⟩
    · rw [smul_zero]
      exact zero_mem _
    · ext i j
      exact map_zero (infPart D)
  | add x y _ _ hx hy =>
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · rw [smul_add]
      exact add_mem (hx.1 γ hγ) (hy.1 γ hγ)
    · rw [smul_add, hx.2.1, hy.2.1]
    · ext i j
      have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx.2.2.1 i) j
      have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy.2.2.1 i) j
      show infPart D (x i j + y i j) = 0
      rw [map_add (infPart D), h1, h2, add_zero]
    · rw [hx.2.2.2 h, hy.2.2.2 h, add_zero]
  | neg x _ hx =>
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · rw [smul_neg]
      exact neg_mem (hx.1 γ hγ)
    · rw [smul_neg, hx.2.1]
    · ext i j
      have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx.2.2.1 i) j
      show infPart D (- x i j) = 0
      rw [map_neg, h1, neg_zero]
    · rw [hx.2.2.2 h, neg_zero]

end GlobalTheory.FinPl
