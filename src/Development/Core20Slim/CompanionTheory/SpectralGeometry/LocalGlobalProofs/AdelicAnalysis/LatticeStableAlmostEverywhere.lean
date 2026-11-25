module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatRat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  filter_upwards [h.compl_mem_cofinite] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [h2]
  exact not_lt.mp hv

def latR {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

def Good {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) : Prop :=
  ∀ k l, algebraMap F (Fv F v) (b.repr (b k * e) l) ∈ v.adicCompletionIntegers F

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (y : Fv F v ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (y * inclR (Fv F v) e) l =
      ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k *
        algebraMap F (Fv F v) (b.repr (b k * e) l) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  simp [inclR, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

theorem mul_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {e : E}
    (he : Good b v e) {y : Fv F v ⊗[F] E} (hy : y ∈ latR b v) : y * inclR (Fv F v) e ∈ latR b v := by
  intro l
  rw [repr_mul]
  exact sum_mem fun k _ => mul_mem (hy k) (he k l)

theorem sum_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ι : Type}
    (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ c ∈ s, f c ∈ latR b v) : ∑ c ∈ s, f c ∈ latR b v := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun c hc => h c hc k

theorem eventually_good {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Good b v e :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_integral _

theorem eventually_good_matrix {d m : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin m) (Fin m) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Good b v (g i j) :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_good b _

omit [NumberField F] in
theorem rmul_rmul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : rmul R (rmul R X A) B = rmul R X (A * B) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [NumberField F] in
theorem rmul_one (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

theorem rmul_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : Matrix (Fin n) (Fin n) E} (hg : ∀ i j, Good b v (g i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v := by
  intro a i
  exact sum_mem_latR _ _ (fun c _ => mul_mem_latR (hg c a) (fun k => hX c i k))

theorem actTup_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : GL (Fin M) E} (hg : ∀ i j, Good b v ((g : Matrix (Fin M) (Fin M) E) i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v := by
  intro a i
  have h : actTup (Fv F v) (bc (inclR (Fv F v)) g) X a i =
      ∑ j, X a j * inclR (Fv F v) ((g : Matrix (Fin M) (Fin M) E) i j) := by
    simp only [actTup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h]
  exact sum_mem_latR _ _ (fun j _ => mul_mem_latR (hg i j) (fun k => hX a j k))

omit [NumberField F] in
theorem actTup_inv {M n : ℕ} (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (bc (inclR R) g⁻¹) (actTup R (bc (inclR R) g) X) = X := by
  funext a
  simp only [actTup, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem one_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F) :
    (1 : Fv F v ⊗[F] E) ∈ latR b v := by
  intro k
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k

theorem consTup_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro hX a i k
    simpa [consTup] using hX a.succ i.succ k
  · intro hX a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consTup] using one_mem_latR h k
      · simp [consTup]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup]
      · simpa [consTup] using hX a i

theorem latV_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b n M
  refine ⟨fun g hg => ?_, fun g => ?_, ?_⟩
  · filter_upwards [eventually_good_matrix b g, eventually_good_matrix b g⁻¹] with v h1 h2 X
    refine ⟨fun hX => ?_, rmul_mem h1⟩
    have hmul : g.map (inclR (F := F) (E := E) (Fv F v)) * g⁻¹.map (inclR (F := F) (E := E) (Fv F v)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg),
        Matrix.map_one _ (map_zero _) (map_one _)]
    have := rmul_mem h2 hX
    rwa [rmul_rmul, hmul, rmul_one] at this
  · filter_upwards [eventually_good_matrix b (g : Matrix (Fin M) (Fin M) E),
      eventually_good_matrix b ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)] with v h1 h2 X
    refine ⟨fun hX => ?_, actTup_mem h1⟩
    have := actTup_mem (g := g⁻¹) h2 hX
    rwa [actTup_inv] at this
  · have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
        algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun k => eventually_integral (b.repr (1 : E) k)
    filter_upwards [h0] with v h X
    exact consTup_mem_iff h X

end GlobalTheory.CompanionTheory.SW.LatRat
