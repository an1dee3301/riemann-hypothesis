module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.FinPl (latMul colMul)
open GlobalTheory.SeeSaw (idV idV_mono)

namespace GlobalTheory.StairCols

variable {D : D7}

theorem exists_coord {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : p.rev ≠ p) :
    ∃ l : Fin B.rank → D.host.E, (∀ i, ∑ k, l k * frameMat B A d.ι k i = 0) ∧
      ∀ q, ∑ k, l k * d.a k q = if q = p then 1 else 0 := by
  classical

  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x := by
    intro x
    exact star_star x
  have hG : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram = B.gram := by
    ext i j
    exact B.herm.eq (B.frame j) (B.frame i)
  have hmul : ∀ {m n q : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (N : Matrix (Fin n) (Fin q) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (M * N) =
        Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) N * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M := by
    intro m n q M N
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hinv : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M) = M := by
    intro m n M
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ]

  have hperp : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram * frameMat B A d.ι = 0 := by
    have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) d.perp
    rw [hmul, hmul, hinv, hG] at h
    rw [Matrix.mul_assoc, h]
    ext i j
    simp [Formalism.UG.cT]
  refine ⟨fun k => (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram) p.rev k, fun i => ?_, fun q => ?_⟩
  · have h := congrFun (congrFun hperp p.rev) i
    rw [Matrix.mul_apply, Matrix.zero_apply] at h
    exact h
  · have h := congrFun (congrFun d.gram p.rev) q
    rw [Matrix.mul_apply] at h
    refine h.trans ?_
    show (if p.rev.1 + q.1 + 1 = c then (if p.rev = q then ε else (1 : D.host.E)) else 0) = _
    by_cases hq : q = p
    · rw [hq]
      have hc : p.rev.1 + p.1 + 1 = c := by
        rw [Fin.val_rev]
        have := p.isLt
        omega
      rw [if_pos hc, if_neg hp, if_pos rfl]
    · have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
        intro hs
        apply hq
        apply Fin.ext
        rw [Fin.val_rev] at hs
        have := p.isLt
        have := q.isLt
        omega
      rw [if_neg hne, if_neg hq]

theorem coord_apply {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (l : Fin B.rank → D.host.E)
    (h0 : ∀ i, ∑ k, l k * frameMat B A d.ι k i = 0) (h1 : ∀ q, ∑ k, l k * d.a k q = if q = p then 1 else 0)
    (z : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    ∑ k, l k * (frameMat B A d.ι *ᵥ z + d.a *ᵥ u) k = u p := by

  have swap : ∀ {n : ℕ} (M : Matrix (Fin B.rank) (Fin n) D.host.E) (w : Fin n → D.host.E),
      ∑ k, l k * (M *ᵥ w) k = ∑ j, (∑ k, l k * M k j) * w j := by
    intro n M w
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, swap, h0, h1, zero_mul,
    Finset.sum_const_zero, zero_add, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (p : Fin n) (w : D.host.E) (k : Fin m) :
    (M *ᵥ Pi.single p w) k = M k p * w := by
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem incA_mul_tmul (e : D.host.E) (x : AF D.host.F) (b : D.host.E) :
    incA D e * (x ⊗ₜ[D.host.F] b) = x ⊗ₜ[D.host.F] (e * b) := by

  rw [GlobalTheory.IdeleAA.tmul_eq, GlobalTheory.IdeleAA.tmul_eq, map_mul]
  ring

theorem col_mem_imp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : p.rev ≠ p)
    (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (s : Set D.host.E) (hs : ∀ x ∈ s, x ∈ 𝔞) (v : GlobalTheory.FinPl.Pl D) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latMul B s (d.lat Λ 𝔟) (· = v) → t ∈ idV (𝔞 * 𝔟 p) v := by
  intro hmem
  obtain ⟨l, h0, h1⟩ := GlobalTheory.StairCols.exists_coord d p hp

  have hφ : latMul B s (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔞 * 𝔟 p) v).comap
      (AddMonoidHom.mk' (fun y : Fin B.rank → AE D => ∑ k, incA D (l k) * y k)
        (fun x y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])) := by
    apply (AddSubgroup.closure_le _).2
    rintro y ⟨α, hα, hsupp, e, he, x, hx, rfl⟩
    obtain ⟨z, hz, u, hu, rfl⟩ := hx
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.mk'_apply]
    have hsum : ∑ k, incA D (l k) * pairA D.host.F 0 α ⊗ₜ[D.host.F] (e * (frameMat B A d.ι *ᵥ z + d.a *ᵥ u) k)
        = pairA D.host.F 0 α ⊗ₜ[D.host.F] (e * u p) := by
      simp only [GlobalTheory.StairCols.incA_mul_tmul, ← TensorProduct.tmul_sum]
      congr 1
      rw [← GlobalTheory.StairCols.coord_apply d p l h0 h1 z u, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum]
    exact AddSubgroup.subset_closure ⟨α, hα, hsupp, e * u p, FractionalIdeal.mul_mem_mul (hs e he) (hu p), rfl⟩
  have ht := hφ hmem
  rw [AddSubgroup.mem_comap, AddMonoidHom.mk'_apply] at ht

  have hread : ∑ k, incA D (l k) * (t * incA D (d.a k p)) = t := by
    have hl := h1 p
    rw [if_pos rfl] at hl
    calc ∑ k, incA D (l k) * (t * incA D (d.a k p)) = t * incA D (∑ k, l k * d.a k p) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
          ring
      _ = t := by rw [hl, map_one, mul_one]
  rwa [hread] at ht

def lineMap {n : ℕ} (w : Fin n → AE D) : AE D →+ (Fin n → AE D) where
  toFun t := fun k => t * w k
  map_zero' := funext fun k => zero_mul _
  map_add' x y := funext fun k => add_mul _ _ _

theorem col_mem_of {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c)
    (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (s : Set D.host.E)
    (hs' : ∀ x ∈ 𝔞, ∃ y ∈ s, ∃ o : 𝓞 D.host.E, x = y * (o : D.host.E)) (v : GlobalTheory.FinPl.Pl D) :
    idV (𝔞 * 𝔟 p) v ≤ (latMul B s (d.lat Λ 𝔟) (· = v)).comap (lineMap fun k => incA D (d.a k p)) := by
  apply (AddSubgroup.closure_le _).2
  rintro y ⟨α, hα, hsupp, e, he, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]

  have key : (fun k => pairA D.host.F 0 α ⊗ₜ[D.host.F] (d.a k p * e)) ∈ latMul B s (d.lat Λ 𝔟) (· = v) := by
    refine FractionalIdeal.mul_induction_on
      (C := fun e => (fun k => pairA D.host.F 0 α ⊗ₜ[D.host.F] (d.a k p * e)) ∈ latMul B s (d.lat Λ 𝔟) (· = v))
      he ?_ ?_
    · intro x hx y hy
      obtain ⟨x', hx', o, rfl⟩ := hs' x hx
      have hoy : (o : D.host.E) * y ∈ 𝔟 p := by
        have h := Submodule.smul_mem (𝔟 p : Submodule (𝓞 D.host.E) D.host.E) o hy
        rwa [Algebra.smul_def] at h
      have hmem : d.a *ᵥ Pi.single p ((o : D.host.E) * y) ∈ d.lat Λ 𝔟 := by
        show ∃ z ∈ Λ, ∃ u : Fin c → D.host.E, (∀ q, u q ∈ 𝔟 q) ∧
          d.a *ᵥ Pi.single p ((o : D.host.E) * y) = frameMat B A d.ι *ᵥ z + d.a *ᵥ u
        refine ⟨0, Λ.zero_mem, Pi.single p ((o : D.host.E) * y), fun q => ?_, ?_⟩
        · by_cases hq : q = p
          · subst hq
            rw [Pi.single_eq_same]
            exact hoy
          · rw [Pi.single_eq_of_ne hq]
            exact (𝔟 q).zero_mem
        · rw [Matrix.mulVec_zero, zero_add]
      apply AddSubgroup.subset_closure
      refine ⟨α, hα, hsupp, x', hx', _, hmem, ?_⟩
      funext k
      rw [GlobalTheory.StairCols.mulVec_single_apply]
      congr 1
      ring
    · intro x y hx hy
      have hsum := add_mem hx hy
      convert hsum using 1
      funext k
      rw [Pi.add_apply, mul_add, TensorProduct.tmul_add]
  convert key using 1
  funext k
  show pairA D.host.F 0 α ⊗ₜ[D.host.F] e * incA D (d.a k p) = _
  rw [mul_comm, GlobalTheory.StairCols.incA_mul_tmul]

theorem col_mem_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : p.rev ≠ p)
    (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (s : Set D.host.E) (hs : ∀ x ∈ s, x ∈ 𝔞)
    (hs' : ∀ x ∈ 𝔞, ∃ y ∈ s, ∃ o : 𝓞 D.host.E, x = y * (o : D.host.E)) (v : GlobalTheory.FinPl.Pl D) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latMul B s (d.lat Λ 𝔟) (· = v) ↔ t ∈ idV (𝔞 * 𝔟 p) v := by
  refine ⟨GlobalTheory.StairCols.col_mem_imp d p hp Λ 𝔟 𝔞 s hs v t, fun ht => ?_⟩
  exact GlobalTheory.StairCols.col_mem_of d p Λ 𝔟 𝔞 s hs' v ht





end GlobalTheory.StairCols

end
