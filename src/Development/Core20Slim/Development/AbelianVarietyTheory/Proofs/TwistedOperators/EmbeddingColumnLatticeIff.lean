module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
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
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UnitaryEmbeddingLine

variable {D : D7}

theorem tmul_mul_inc (α : AF D.host.F) (b x : D.host.E) :
    (α ⊗ₜ[D.host.F] b : AE D) * incA D x = α ⊗ₜ[D.host.F] (b * x) := by
  change (α ⊗ₜ[D.host.F] b) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem exists_coeff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (p : Fin c) :
    ∃ r : Fin B.rank → D.host.E, ∀ (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E),
      r ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = u p := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have h2 : (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 := d.perp
  have h3 : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at this
    exact this
  have hκ : antiDiagonalSignGramMatrix c ε p.rev p ≠ 0 := by
    have := p.2
    have e : p.rev.1 + p.1 + 1 = c := by rw [Fin.val_rev]; omega
    simp only [antiDiagonalSignGramMatrix, if_pos e]
    split_ifs
    · exact hε
    · exact one_ne_zero
  refine ⟨(antiDiagonalSignGramMatrix c ε p.rev p)⁻¹ • (d.aᴴ * B.gram) p.rev, fun y u => ?_⟩
  have e : (d.aᴴ * B.gram) p.rev ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) =
      ((d.aᴴ * B.gram) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u)) p.rev := rfl
  rw [smul_dotProduct, e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h3, zero_mulVec, zero_add]
  have e2 : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = antiDiagonalSignGramMatrix c ε p.rev p * u p := by
    show ∑ q, antiDiagonalSignGramMatrix c ε p.rev q * u q = _
    refine Finset.sum_eq_single p (fun q _ hq => ?_) (by simp)
    have := p.2
    have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
      intro h; apply hq; apply Fin.ext; rw [Fin.val_rev] at h; omega
    simp only [antiDiagonalSignGramMatrix, if_neg hne, zero_mul]
  rw [e2, smul_eq_mul, inv_mul_cancel_left₀ hκ]

def formHom {R : Type} [CommRing R] {n : ℕ} (r : Fin n → R) : (Fin n → R) →+ R where
  toFun y := ∑ k, y k * r k
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

def lineHom {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) : R →+ (Fin n → R) where
  toFun s := fun k => s * a k
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp only [Pi.add_apply, add_mul]

theorem form_line {K R : Type} [CommRing K] [CommRing R] (f : K →+* R) {n : ℕ} (r a : Fin n → K) (h : r ⬝ᵥ a = 1) (s : R) :
    formHom (fun k => f (r k)) (fun k => s * f (a k)) = s := by
  show ∑ k, s * f (a k) * f (r k) = s
  simp only [mul_assoc, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.mul_sum, ← map_sum]
  have : ∑ k, a k * r k = 1 := by
    rw [← h, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this, map_one, mul_one]

theorem col_eq {K : Type} [CommRing K] {n k c : ℕ} (M : Matrix (Fin n) (Fin k) K) (a : Matrix (Fin n) (Fin c) K) (p : Fin c)
    (b : K) : (fun i => b * a i p) = M *ᵥ 0 + a *ᵥ Pi.single p b := by
  funext k; simp [mul_comm]

theorem line_mp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I) (s : AE D)
    (h : (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)) : s ∈ GlobalTheory.SeeSaw.idV I v := by
  obtain ⟨r, hr⟩ := exists_coeff d hε p
  have key : GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ≤ (GlobalTheory.SeeSaw.idV I v).comap (formHom fun k => incA D (r k)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, a, ha, x, ⟨y0, -, u, hu, hx⟩, rfl⟩
    have e : ∑ k, ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x k) : AE D) * incA D (r k) =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) := by
      rw [Finset.sum_congr rfl fun k _ => tmul_mul_inc (pairA D.host.F 0 α) (a * x k) (r k),
        ← TensorProduct.tmul_sum, ← hr y0 u, ← hx, dotProduct, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    have h2 : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) ∈ GlobalTheory.SeeSaw.idV I v :=
      AddSubgroup.subset_closure ⟨α, hα, hαv, _, hI a ha _ (hu p), rfl⟩
    rw [← e] at h2
    exact h2
  have h1 := hr 0 (Pi.single p 1)
  rw [← col_eq, Pi.single_eq_same] at h1
  simp only [one_mul] at h1
  have := AddSubgroup.mem_comap.1 (key h)
  rwa [form_line (incA D) r (fun k => d.a k p) h1 s] at this

theorem line_mpr {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) (h : s ∈ GlobalTheory.SeeSaw.idV I v) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) := by
  have key : GlobalTheory.SeeSaw.idV I v ≤ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, z, hz, rfl⟩
    refine hI' (fun z => ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] z : AE D) ∈
      (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))) ?_ ?_ z hz
    · intro a ha b hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, fun k => b * d.a k p,
        ⟨0, Λ.zero_mem, Pi.single p b, fun q => ?_, col_eq _ _ p b⟩, ?_⟩)
      · by_cases hq : q = p
        · subst hq; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
      · funext k
        exact (tmul_mul_inc _ _ _).trans (congrArg _ (mul_assoc _ _ _))
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
  exact AddSubgroup.mem_comap.1 (key h)

theorem line_gen {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV I v :=
  ⟨line_mp d Λ 𝔟 p v S I hε hI s, line_mpr d Λ 𝔟 p v S I hI' s⟩

theorem embedding_line_mem_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  intro D A B c ε d hε Λ 𝔟 p v s
  refine ⟨line_gen d Λ 𝔟 p v {1} (𝔟 p) hε ?_ ?_ s, line_gen d Λ 𝔟 p v {a | a ∈ D.host.AA} _ hε ?_ ?_ s⟩
  · rintro a rfl b hb; rwa [one_mul]
  · intro C h _ z hz
    have := h 1 rfl z hz
    rwa [one_mul] at this
  · intro a ha b hb; exact FractionalIdeal.mul_mem_mul ha hb
  · intro C h h' z hz
    exact FractionalIdeal.mul_induction_on hz h h'

end GlobalTheory.AscFin.UnitaryEmbeddingLine

end
