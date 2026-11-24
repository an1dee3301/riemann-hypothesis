module

public import Formalism.PeriodIntegrals.LatCountG
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.EnergyIdentity
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
public import Formalism.HermitianLattices.StatementMass

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.AfT

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct
open Formalism.MainNotions.S

section Fin

variable (F : Type) [Field F] [NumberField F]

theorem natCast_apply (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (N : Af F) v = (N : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (Af F)) N, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap F (v.adicCompletion F)) N

theorem natCast_mul_apply (N : ℕ) (z : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : Af F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply]
  rfl

theorem norm_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    rw [show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl,
      map_natCast]
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hval

theorem mem_int_of_norm_le_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (h : ‖x‖ ≤ 1) :
    x ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((Valued.toNormedField.norm_le_one_iff).1 h)


theorem exists_nat_mul_intAd (x : Af F) : ∃ N : ℕ, 1 ≤ N ∧ (N : Af F) * x ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ x v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 x.2
  set S := hfin.toFinset with hS
  set c : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ S, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one F v c (Finset.dvd_prod_of_mem _ hv)
  have hev : ∀ v ∈ S, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k * ‖x v‖ < 1 := by
    intro v hv
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).mul_const ‖x v‖
    rw [zero_mul] at ht
    exact ht.eventually (Iio_mem_nhds one_pos)
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finset S).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun v => ?_⟩
  show ((((c ^ k : ℕ)) : Af F) * x) v ∈ v.adicCompletionIntegers F
  rw [natCast_mul_apply]
  by_cases hv : v ∈ S
  · apply mem_int_of_norm_le_one
    rw [norm_mul, Nat.cast_pow, norm_pow]
    exact (hk v hv).le
  · have hxv : x v ∈ v.adicCompletionIntegers F := by
      rw [hS, Set.Finite.mem_toFinset] at hv
      simpa using hv
    exact mul_mem (natCast_mem _ _) hxv


end Fin

theorem exists_nat_den {E : Type} [Field E] [NumberField E] (s : Finset E) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ s, (d : E) * x ∈ Formalism.UG.intOE E := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun x hx => ?_⟩
  have hi : IsIntegral ℤ ((y.natAbs : E) * x) := by
    have hyx := h x hx
    rw [zsmul_eq_mul] at hyx
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice y with h' | h'
    · rw [h']; exact hyx
    · rw [h', Int.cast_neg, neg_mul]; exact hyx.neg
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hi
  exact ⟨a, ha⟩

variable (I : AutInst)

abbrev AEf : Type := I.E ⊗[I.F] Af I.F

theorem inclE_mem_IntAf {x : I.E} (hx : x ∈ Formalism.UG.intOE I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) x ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem includeRight_mem_IntAf {a : Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) :
    (Algebra.TensorProduct.includeRight a : AEf I) ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem tmul_eq (e : I.E) (a : Af I.F) :
    (e ⊗ₜ[I.F] a : AEf I) = Formalism.UG.inclE (F := I.F) (Af I.F) e * Algebra.TensorProduct.includeRight a := by
  simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]

theorem natCast_mul_mem {N : ℕ} {y : AEf I} (hy : y ∈ IntAf I.F I.E) : (N : AEf I) * y ∈ IntAf I.F I.E :=
  mul_mem (natCast_mem _ N) hy

theorem exists_nat_mul_mem (t : AEf I) : ∃ N : ℕ, 1 ≤ N ∧ (N : AEf I) * t ∈ IntAf I.F I.E := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, le_rfl, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨d, hd, hde⟩ := exists_nat_den (E := I.E) {e}
    obtain ⟨M, hM, hMa⟩ := exists_nat_mul_intAd I.F a
    refine ⟨d * M, Nat.mul_pos hd hM, ?_⟩
    have h1 := inclE_mem_IntAf I (hde e (Finset.mem_singleton_self e))
    have h2 := includeRight_mem_IntAf I hMa
    rw [map_mul, map_natCast] at h1
    rw [map_mul, map_natCast] at h2
    rw [tmul_eq]
    have e' : ((d * M : ℕ) : AEf I) * (Formalism.UG.inclE (F := I.F) (Af I.F) e * Algebra.TensorProduct.includeRight a) =
        ((d : AEf I) * Formalism.UG.inclE (F := I.F) (Af I.F) e) * ((M : AEf I) * Algebra.TensorProduct.includeRight a) := by
      push_cast; ring
    rw [e']
    exact mul_mem h1 h2
  | add s t hs ht =>
    obtain ⟨N1, h1, hs⟩ := hs
    obtain ⟨N2, h2, ht⟩ := ht
    refine ⟨N1 * N2, Nat.mul_pos h1 h2, ?_⟩
    have e' : ((N1 * N2 : ℕ) : AEf I) * (s + t) = (N2 : AEf I) * ((N1 : AEf I) * s) + (N1 : AEf I) * ((N2 : AEf I) * t) := by
      push_cast; ring
    rw [e']
    exact add_mem (natCast_mul_mem I hs) (natCast_mul_mem I ht)

def bsub (N : ℕ) : AddSubgroup (AEf I) :=
  (IntAf I.F I.E).toAddSubgroup.map (AddMonoidHom.mulLeft (N : AEf I))

theorem mem_bsub {N : ℕ} {x : AEf I} : x ∈ bsub I N ↔ ∃ z ∈ IntAf I.F I.E, (N : AEf I) * z = x := by
  simp [bsub]

theorem bsub_mul_le {N M : ℕ} (h : M ∣ N) : bsub I N ≤ bsub I M := by
  intro x hx
  obtain ⟨k, rfl⟩ := h
  obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hx
  refine (mem_bsub I).2 ⟨(k : AEf I) * z, natCast_mul_mem I hz, ?_⟩
  push_cast; ring

def bas (k : ℕ) : AddSubgroup (AEf I) := bsub I (k + 1)

theorem ringSubgroupsBasis_bas : RingSubgroupsBasis (bas I) := by
  refine RingSubgroupsBasis.of_comm (bas I) ?_ ?_ ?_
  · intro i j
    refine ⟨(i + 1) * (j + 1) - 1, le_inf ?_ ?_⟩
    · apply bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]
      exact dvd_mul_right _ _
    · apply bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]
      exact dvd_mul_left _ _
  · intro i
    refine ⟨i, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hx
    obtain ⟨w, hw, rfl⟩ := (mem_bsub I).1 hy
    refine (mem_bsub I).2 ⟨z * (((i + 1 : ℕ) : AEf I) * w), mul_mem hz (natCast_mul_mem I hw), ?_⟩
    ring
  · intro x i
    obtain ⟨N, hN, hx⟩ := exists_nat_mul_mem I x
    refine ⟨(i + 1) * N - 1, ?_⟩
    intro y hy
    have hpos : 1 ≤ (i + 1) * N := Nat.mul_pos (Nat.succ_pos i) hN
    change y ∈ bsub I ((i + 1) * N - 1 + 1) at hy
    rw [Nat.sub_add_cancel hpos] at hy
    obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hy
    show x * (((i + 1) * N : ℕ) * z) ∈ bsub I (i + 1)
    refine (mem_bsub I).2 ⟨((N : AEf I) * x) * z, mul_mem hx hz, ?_⟩
    push_cast; ring

@[instance_reducible] def tAf : TopologicalSpace (AEf I) := (ringSubgroupsBasis_bas I).topology




section T2

variable {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E)





end T2








end PI.IwaMeasEx.AfT
