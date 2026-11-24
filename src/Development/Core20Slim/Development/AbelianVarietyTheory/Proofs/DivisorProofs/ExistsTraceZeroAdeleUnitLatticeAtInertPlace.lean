module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegr
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.UniformSpace.Completion

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph.Scal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem disc_sub_sq_notMem (v : Pl (F := F)) (b c t : 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal) : t ^ 2 - (b ^ 2 - 4 * c) ∉ v.asIdeal := by
  intro h
  obtain ⟨s, a, ha, hs⟩ := v.isMaximal.exists_inv h2
  apply hroot (s * (t - b))
  have h4 : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) ∈ v.asIdeal := by
    have e : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) =
        (t ^ 2 - (b ^ 2 - 4 * c)) + a * ((t - b) * (a * (t - b) - 2 * t)) := by
      have : a = 1 - s * 2 := by linear_combination hs
      subst this
      ring
    rw [e]
    exact add_mem h (Ideal.mul_mem_right _ _ ha)
  exact ((v.isPrime.mem_or_mem ((v.isPrime.mem_or_mem h4).resolve_left h2)).resolve_left h2)

theorem exists_delta (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∃ (δ : 𝓞 E) (D : 𝓞 F), σ (δ : E) = -(δ : E) ∧ (δ : E) * δ = algebraMap F E (D : F) ∧ D ∉ v.asIdeal ∧
      1 - D ∉ v.asIdeal := by
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hin]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hc, hroot⟩ := GlobalTheory.InertUnitNorm.exists_integral_gen σ hσ v hp
  have hδ : ((2 * a + algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = 2 * (a : E) + algebraMap F E (b : F) := rfl
  have hD : ((b ^ 2 - 4 * c : 𝓞 F) : F) = (b : F) ^ 2 - 4 * (c : F) := rfl
  refine ⟨2 * a + algebraMap (𝓞 F) (𝓞 E) b, b ^ 2 - 4 * c, ?_, ?_, ?_, ?_⟩
  · rw [hδ, map_add (f := _), map_mul, map_ofNat, AlgHom.commutes, hc]
    ring
  · rw [hδ, hD, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hq
  · intro h
    apply disc_sub_sq_notMem v b c 0 h2 hroot
    simpa using neg_mem h
  · simpa using disc_sub_sq_notMem v b c 1 h2 hroot

theorem exists_inv (v : Pl (F := F)) (D : 𝓞 F) (hD : D ∉ v.asIdeal) :
    ∃ c : Fv F v, c ∈ v.adicCompletionIntegers F ∧ c * algebraMap F (Fv F v) (D : F) = 1 := by
  have h1 : Valued.v (algebraMap F (Fv F v) (D : F)) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (D : F)
    have h' : v.valuation F (D : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hD
    rw [← h', ← h]
    rfl
  have h0 : algebraMap F (Fv F v) (D : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  refine ⟨(algebraMap F (Fv F v) (D : F))⁻¹, ?_, inv_mul_cancel₀ h0⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {z : M} (hz : At (evFin F v) z)
    {a : AF F} (ha : evFin F v a = 1) : a • z = z := by
  have h := hz (a - 1) (by rw [map_sub, map_one, ha, sub_self])
  rwa [sub_smul, one_smul, sub_eq_zero] at h

theorem at_of_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    At (evFin F v) z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    intro u hu
    rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]

theorem lift_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (o : 𝓞 E) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    (GlobalTheory.LatVac.liftV v c • inclR (F := F) (AF F) (o : E)) • z ∈ latAt W v :=
  GlobalTheory.InertLocFrame.Lat.smul_mem_latAt W (AddSubgroup.subset_closure
    ⟨_, GlobalTheory.LatVac.at_liftV v c, by rwa [GlobalTheory.LatVac.evFin_liftV], o, rfl⟩) hz

end GlobalTheory.InertSph.Scal

namespace GlobalTheory.InertSph


open GlobalTheory.InertSph.Scal GlobalTheory.LatVac in
theorem exists_traceZero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : AE F E, At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  intro F E _ _ _ _ _ σ B hB d W v w hin
  obtain ⟨δ, D, hσ, hsq, hD, hD1⟩ := exists_delta σ hB.cm v w hin (hB.inert v w hin).1
  obtain ⟨c, hc, hcD⟩ := exists_inv v D hD
  obtain ⟨c', hc', hcD'⟩ := exists_inv v (1 - D) hD1
  have hcD'' : c' * (1 - algebraMap F (Fv F v) (D : F)) = 1 := by
    rwa [show ((1 - D : 𝓞 F) : F) = 1 - (D : F) from rfl, map_sub, map_one] at hcD'
  set x : AE F E := inclR (F := F) (AF F) (δ : E) with hx
  have hxx : x * x = algebraMap (AF F) (AE F E) (algebraMap F (AF F) (D : F)) := by
    rw [hx, ← map_mul, hsq, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes _
  have hp : inclR (F := F) (AF F) ((1 + δ : 𝓞 E) : E) = 1 + x := by
    rw [show ((1 + δ : 𝓞 E) : E) = 1 + (δ : E) from rfl, map_add (f := _), map_one]
  have hm : inclR (F := F) (AF F) ((1 - δ : 𝓞 E) : E) = 1 - x := by
    rw [show ((1 - δ : 𝓞 E) : E) = 1 - (δ : E) from rfl, map_sub, map_one]
  have he : liftV v (1 : Fv F v) * liftV v c' = liftV v c' :=
    smul_eq_of_at (at_liftV v c') (evFin_liftV v 1)
  have he' : algebraMap (AF F) (AE F E) (liftV v (1 : Fv F v)) * algebraMap (AF F) (AE F E) (liftV v c') =
      algebraMap (AF F) (AE F E) (liftV v c') := by rw [← map_mul, he]
  have key : ∀ z ∈ latAt W v, ∀ a : AF F, evFin F v a = 1 → algebraMap (AF F) (AE F E) a • z = z := by
    intro z hz a ha
    rw [algebraMap_smul]
    exact smul_eq_of_at (at_of_mem_latAt W v hz) ha
  have hu : evFin F v (liftV v c' * (1 - algebraMap F (AF F) (D : F))) = 1 := by
    rw [map_mul, map_sub, map_one, evFin_liftV, AlgHom.commutes, hcD'']
  refine ⟨liftV v 1 • x, liftV v c • x, liftV v c' • (1 - x), liftV v c' • (1 + x), ?_, ?_, fun z hz =>
    ⟨lift_smul_mem W v (one_mem _) δ hz, lift_smul_mem W v hc δ hz, hm ▸ lift_smul_mem W v hc' (1 - δ) hz,
      hp ▸ lift_smul_mem W v hc' (1 + δ) hz, ?_, ?_, ?_⟩⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]
  · have h : cA σ x = -x := by
      have h1 : cA σ x = inclR (F := F) (AF F) (σ (δ : E)) := by
        simp [hx, cA, inclR]
      rw [h1, hσ, map_neg]
    rw [map_smul, h, smul_neg]
  · have h := key z hz (liftV v 1 * liftV v c * algebraMap F (AF F) (D : F)) (by
      rw [map_mul, map_mul, evFin_liftV, evFin_liftV, AlgHom.commutes, one_mul, hcD])
    convert h using 2
    simp only [Algebra.smul_def, map_mul, ← hxx]
    ring
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (x * (1 - x)) * he'
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (-x * (1 + x)) * he'

end GlobalTheory.InertSph

end
