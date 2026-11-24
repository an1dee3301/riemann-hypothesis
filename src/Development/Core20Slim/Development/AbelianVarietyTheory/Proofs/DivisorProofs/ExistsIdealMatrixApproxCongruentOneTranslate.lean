module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongApprox

theorem inc_mem_OhE (D : D7) (x : 𝓞 D.host.E) : inc D (x : D.host.E) ∈ OhE D :=
  Formalism.UG.P.easyc_inclE_mem _ _ _ (RingHom.mem_range.2 ⟨x, rfl⟩)

theorem exists_int_approx (D : D7) (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ b : 𝓞 D.host.E, ∃ w ∈ OhE D, s = inc D (b : D.host.E) + (n : AE D) * w := by
  rw [← GlobalTheory.AdelicApprox.levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨b, t, ht, h⟩

theorem OhE_le_IhE_top (D : D7) (s : AE D) (hs : s ∈ OhE D) : s ∈ IhE D ⊤ := by
  have h := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ s hs
  simpa [Ideal.absNorm_top] using h

theorem mul_mem_hatId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (x : AE D) (hx : x ∈ OhE D)
    (t : AE D) (ht : t ∈ hatId D 𝔪) : x * t ∈ hatId D 𝔪 := by
  unfold hatId at ht ⊢
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (t : AE D)
    (ht : t ∈ hatId D 𝔪) :
    ∃ b ∈ 𝔪, ∃ y ∈ IhE D ⊤, inc D (b : D.host.E) - t = (m : AE D) * y := by
  unfold hatId at ht
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    obtain ⟨c, w, hw, hsw⟩ := exists_int_approx D m hm s hs
    refine ⟨b * c, Ideal.mul_mem_right c 𝔪 hb, -(inc D (b : D.host.E) * w),
      OhE_le_IhE_top D _ (neg_mem (mul_mem (inc_mem_OhE D b) hw)), ?_⟩
    rw [hsw]
    push_cast
    rw [map_mul]
    ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    obtain ⟨b', hb', u', hu', h'⟩ := hy'
    refine ⟨b + b', add_mem hb hb', u + u', add_mem hu hu', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination h + h'
  | neg y _ hy =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    refine ⟨-b, neg_mem hb, -u, neg_mem hu, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -h

end GlobalTheory.CongApprox

namespace GlobalTheory.CongApprox

theorem exists_closeTo_congOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (k : GA D a), k ∈ intG D a → CongOne D 𝔪 k → ∀ (z : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ CloseTo D ⊤ m (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) z (z + w) := by
  intro D 𝔪 _ a d k hk hcong z _ m hm
  have hinv : CongOne D 𝔪 k⁻¹ := congOne_inv hk hcong
  set K : Matrix (Fin a) (Fin a) (AE D) := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  set T : Matrix (Fin d) (Fin a) (AE D) := z.map (inc D) * (K - 1) with hT
  have hTmem : ∀ i j, T i j ∈ hatId D 𝔪 := by
    intro i j
    rw [hT, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    obtain ⟨b, hb⟩ := ‹∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)› i l
    rw [Matrix.map_apply, hb]
    exact mul_mem_hatId D 𝔪 _ (inc_mem_OhE D b) _ (hinv l j)
  choose b hb y hy hby using fun i j => exists_mem_approx D 𝔪 m hm (T i j) (hTmem i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have hKinv : (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = K := by
    rw [hK, Subgroup.coe_inv]
  have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
  have hzK : z.map (inc D) * K = z.map (inc D) + T := by
    rw [hT, Matrix.mul_sub, Matrix.mul_one]; abel
  have key : ∀ i j, ((z + Matrix.of fun i j => (b i j : D.host.E)).map (inc D) -
      (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * z.map (inc D) *
        (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j =
      inc D (b i j : D.host.E) - T i j := by
    intro i j
    rw [e1, Matrix.one_mul, hKinv, hzK, Matrix.map_add _ (map_add (inc D))]
    simp [Matrix.map_apply]
  unfold CloseTo
  exact fun i j => ⟨y i j, hy i j, (key i j).trans (hby i j)⟩

end GlobalTheory.CongApprox
