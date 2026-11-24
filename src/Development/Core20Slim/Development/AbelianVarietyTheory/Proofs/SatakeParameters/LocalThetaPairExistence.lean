module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Batteries.Logic
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

section LatModelAux

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMatSub (n n' : ℕ) : AddSubgroup (Matrix (Fin n') (Fin n) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := by
    intro a b ha hb i j
    exact (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := by
    intro a ha i j
    exact (Formalism.UG.intL L).neg_mem (ha i j)

theorem mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem glint_entry {m : ℕ} {g : GL (Fin m) L} (hg : g ∈ Formalism.UG.GLint (Fin m) (Formalism.UG.intL L)) (i j : Fin m) :
    (g : Matrix (Fin m) (Fin m) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg
  exact (k.val i j).2

theorem matMul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem locH_conj (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (δ : L) (hδ : σ δ = -δ) {n n' : ℕ}
    (JS : GL (Fin n) L) (JT : GL (Fin n') L)
    (hS : ∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i)
    (hT : ∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i)
    (x y : Matrix (Fin n') (Fin n) L) :
    σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x := by
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  have hSm : (JS : Matrix (Fin n) (Fin n) L).map σ = (JS : Matrix (Fin n) (Fin n) L)ᵀ := by
    ext i j; simp [hS]
  have hTm : (JT : Matrix (Fin n') (Fin n') L).map σ = (JT : Matrix (Fin n') (Fin n') L)ᵀ := by
    ext i j; simp [hT]
  have hPJ : P * (JS : Matrix (Fin n) (Fin n) L) = 1 := by rw [hPdef]; exact JS.inv_mul
  have h1 : P.map σ * (JS : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← hSm, ← Matrix.map_mul, hPJ]; exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have h2 : (JS : Matrix (Fin n) (Fin n) L) * (P.map σ)ᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : (P.map σ)ᵀ = P := by
    calc (P.map σ)ᵀ = (P * (JS : Matrix (Fin n) (Fin n) L)) * (P.map σ)ᵀ := by rw [hPJ, Matrix.one_mul]
      _ = P := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have hPm : P.map σ = Pᵀ := by
    have := congrArg Matrix.transpose h3
    rwa [Matrix.transpose_transpose] at this
  have htr : ∀ A : Matrix (Fin n) (Fin n) L, σ (Matrix.trace A) = Matrix.trace (A.map σ) := by
    intro A; simp [Matrix.trace, map_sum]
  have hyy : (y.map σ).map σ = y := by ext i j; simp [hσ]
  unfold locH
  rw [← hPdef, map_mul, hδ, htr]
  simp only [Matrix.map_mul, hPm, Matrix.transpose_map, hyy, hTm]
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc P, Matrix.mul_assoc P, Matrix.trace_mul_comm P]
  simp only [Matrix.mul_assoc]
  ring

end LatModelAux

end GlobalTheory.Hk3

namespace GlobalTheory.Hk3

section LatModelAux2

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem locH_sub_right (σ : L →+* L) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L)
    (u x y : Matrix (Fin n') (Fin n) L) :
    locH σ δ JS JT u (x - y) = locH σ δ JS JT u x - locH σ δ JS JT u y := by
  have hm : (x - y).map σ = x.map σ - y.map σ := by ext i j; simp
  unfold locH
  rw [hm, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub, mul_sub]

theorem int_of_psi {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) (ψ : AddChar L ℂ)
    (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (w : L)
    (hw : ∀ b ∈ Formalism.UG.intL L, ψ (b * w + σ (b * w)) = 1) : w ∈ Formalism.UG.intL L := by
  obtain ⟨hσ, hv, hϖ, hvϖ, ⟨x0, hx0, hd⟩, -, -⟩ := hU
  obtain ⟨a0, ha0, hσa, hψa⟩ := hne
  by_contra hwi
  have hwv : 1 < Valued.v w := not_le.mp hwi
  have hw0 : w ≠ 0 := by rintro rfl; simp at hwv
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hvϖ
  have hd0 : σ x0 - x0 ≠ 0 := by intro h; rw [h] at hd; simp at hd
  have h1 : 1 ≤ Valued.v (ϖ * w) := by
    rw [map_mul, hvϖ]
    obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp (zero_lt_one.trans hwv).ne'
    rw [← hk] at hwv ⊢
    rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe]
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hwv
    have : (0 : ℤ) < Multiplicative.toAdd k := hwv
    show (0 : ℤ) ≤ -1 + Multiplicative.toAdd k
    omega
  have hinv : (ϖ * w)⁻¹ ∈ Formalism.UG.intL L := by
    rw [mem_intL_iff, map_inv₀]; exact inv_le_one_of_one_le₀ h1
  set e := x0 / (x0 - σ x0) with he
  have hse : e + σ e = 1 := by
    have hd1 : x0 - σ x0 ≠ 0 := by intro h; apply hd0; rw [← neg_sub, h, neg_zero]
    rw [he, map_div₀, map_sub, hσ]
    field_simp
    ring
  have hei : e ∈ Formalism.UG.intL L := by
    rw [mem_intL_iff, he, map_div₀]
    have : Valued.v (x0 - σ x0) = 1 := by rw [← neg_sub, Valuation.map_neg, hd]
    rw [this, div_one]; exact hx0
  set b := e * a0 * (ϖ * w)⁻¹ with hb
  have hbi : b ∈ Formalism.UG.intL L := Subring.mul_mem _ (Subring.mul_mem _ hei ha0) hinv
  have hbw : b * w = e * (ϖ⁻¹ * a0) := by rw [hb]; field_simp
  have key : b * w + σ (b * w) = ϖ⁻¹ * a0 := by
    rw [hbw, map_mul, map_mul, map_inv₀, hϖ, hσa, ← add_mul, hse, one_mul]
  exact hψa (key ▸ hw b hbi)

end LatModelAux2

end GlobalTheory.Hk3

namespace GlobalTheory.Hk3

section LatModelAux3

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_of_psi {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) {δ : L} (hδ : Valued.v δ = 1)
    {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L}
    (hJS : JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (hJT : JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L))
    (ψ : AddChar L ℂ) (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (z : Matrix (Fin n') (Fin n) L)
    (hz : ∀ u ∈ intMatSub (L := L) n n', ψ (locH σ δ JS JT u z + σ (locH σ δ JS JT u z)) = 1) :
    z ∈ intMatSub (L := L) n n' := by
  intro i j
  have hJTi : (JT⁻¹ : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) := Subgroup.inv_mem _ hJT
  have hw : δ * σ (z i j) ∈ Formalism.UG.intL L := by
    refine int_of_psi hU ψ hne _ (fun b hb => ?_)
    set u : Matrix (Fin n') (Fin n) L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.single i j b *
      (JS : Matrix (Fin n) (Fin n) L) with hu
    have huI : u ∈ intMatSub (L := L) n n' := by
      intro k l
      refine matMul_int (matMul_int (glint_entry hJTi) ?_) (glint_entry hJS) k l
      intro a c
      rw [Matrix.single_apply]
      split_ifs
      · exact hb
      · exact (Formalism.UG.intL L).zero_mem
    have hloc : locH σ δ JS JT u z = b * (δ * σ (z i j)) := by
      unfold locH
      rw [hu]
      have e1 : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (z.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) *
          (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.single i j b * (JS : Matrix (Fin n) (Fin n) L)) =
          ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((z.map σ)ᵀ * Matrix.single i j b) * (JS : Matrix (Fin n) (Fin n) L) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (JT : Matrix (Fin n') (Fin n') L), JT.mul_inv, Matrix.one_mul]
      rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, JS.mul_inv, Matrix.one_mul, Matrix.trace_mul_single]
      simp only [Matrix.transpose_apply, Matrix.map_apply, op_smul_eq_mul]
      ring
    rw [← hloc]
    exact hz u huI
  have hv := hU.2.1
  rw [mem_intL_iff, map_mul, hδ, one_mul, hv] at hw
  exact hw

theorem eig_indep {M : Type} [AddCommGroup M] [Module ℂ M] {ι U : Type} [DecidableEq ι]
    (T : U → Module.End ℂ M) (χ : ι → U → ℂ) (v : ι → M) (hv : ∀ i u, T u (v i) = χ i u • v i)
    (s : Finset ι) (hχ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ u, χ i u ≠ χ j u) :
    ∀ C : ι → ℂ, ∑ i ∈ s, C i • v i = 0 → ∀ i ∈ s, C i • v i = 0 := by
  induction s using Finset.induction_on with
  | empty => intro C _ i hi; simp at hi
  | insert a s ha ih =>
    intro C hC
    rw [Finset.sum_insert ha] at hC
    have hrest : ∀ i ∈ s, C i • v i = 0 := by
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      obtain ⟨u, hu⟩ := hχ i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s) hia
      have hS : ∑ k ∈ s, (C k * (χ k u - χ a u)) • v k = 0 := by
        have e1 : T u (∑ k ∈ s, C k • v k) = ∑ k ∈ s, (C k * χ k u) • v k := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum, map_smul, hv, smul_smul]
        have e2 : ∑ k ∈ s, C k • v k = -(C a • v a) := eq_neg_of_add_eq_zero_right hC
        have e3 : ∑ k ∈ s, (C k * (χ k u - χ a u)) • v k =
            T u (∑ k ∈ s, C k • v k) - χ a u • ∑ k ∈ s, C k • v k := by
          rw [e1, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_smul, ← sub_smul]; ring_nf
        rw [e3, e2, map_neg, map_smul, hv, smul_smul, smul_neg, smul_smul, mul_comm, sub_self]
      have := ih (fun k hk l hl hkl => hχ k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl)
        (fun k => C k * (χ k u - χ a u)) hS i hi
      rw [mul_comm, mul_smul, smul_eq_zero] at this
      exact this.resolve_left (sub_ne_zero.mpr hu)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_eq_zero hrest, add_zero] at hC; exact hC
    · exact hrest i hi

end LatModelAux3

end GlobalTheory.Hk3

namespace GlobalTheory.Hk3


end GlobalTheory.Hk3
