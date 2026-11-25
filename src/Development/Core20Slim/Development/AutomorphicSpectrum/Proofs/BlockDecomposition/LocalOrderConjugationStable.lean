module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Shear

theorem measurePreserving_of_compactOpen {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] (T S : G → G) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hT : Continuous T) (hS : Continuous S) (hST : ∀ x, S (T x) = x) (hTS : ∀ x, T (S x) = x)
    (K : Set G) (hKc : IsCompact K) (hKo : IsOpen K) (hKn : K.Nonempty) (hK : T ⁻¹' K = K) :
    MeasurePreserving T μ μ := by
  let e : G ≃+ G := AddEquiv.mk' ⟨T, S, hST, hTS⟩ hadd
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hT hS
  have hTm : Measurable T := hT.measurable
  have hsm := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ) μ
  have hmapK : Measure.map e μ K = μ K := by
    change Measure.map T μ K = μ K
    rw [Measure.map_apply hTm hKo.measurableSet, hK]
  have h0 : μ K ≠ 0 := hKo.measure_ne_zero μ hKn
  have ht : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  set c := Measure.addHaarScalarFactor (Measure.map e μ) μ with hc
  have hc1 : c = 1 := by
    have h := congrArg (fun m : Measure G => m K) hsm
    simp only [Measure.smul_apply, hmapK] at h
    have h' : (1 : ℝ≥0∞) * μ K = (c : ℝ≥0∞) * μ K := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using h
    have := (ENNReal.mul_left_inj h0 ht).1 h'
    exact_mod_cast this.symm
  refine ⟨hTm, ?_⟩
  change Measure.map e μ = μ
  rw [hsm, hc1, one_smul]

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    GlobalTheory.CompanionTheory.SW.rmul R X (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = X := by
  funext a i
  simp [GlobalTheory.CompanionTheory.SW.rmul, Matrix.one_apply]

theorem rmul_add {M n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    GlobalTheory.CompanionTheory.SW.rmul R (X + Y) g = GlobalTheory.CompanionTheory.SW.rmul R X g + GlobalTheory.CompanionTheory.SW.rmul R Y g := by
  funext a i
  simp [GlobalTheory.CompanionTheory.SW.rmul, add_mul, Finset.sum_add_distrib]

theorem negCol_self {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : negCol R l a l = 1 := by
  simp [negCol]

theorem negCol_negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) (hl : a l = 1) :
    negCol R l (negCol R l a) = a := by
  funext i
  by_cases h : i = l
  · subst h; simp [negCol, hl]
  · simp [negCol, h]

theorem eMat_mem {n : ℕ} (O : Subring (R ⊗[F] E)) (l : Fin n) (a : Fin n → R ⊗[F] E)
    (ha : ∀ i, a i ∈ O) (i k : Fin n) : eMat R l a i k ∈ O := by
  simp only [eMat, Matrix.updateCol_apply, Matrix.one_apply]
  split_ifs
  · exact ha i
  · exact O.one_mem
  · exact O.zero_mem

theorem rmul_mem {M n : ℕ} (O : Subring (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hg : ∀ i k, g i k ∈ O)
    (hX : X ∈ tupIn R (O : Set (R ⊗[F] E))) :
    GlobalTheory.CompanionTheory.SW.rmul R X g ∈ tupIn R (O : Set (R ⊗[F] E)) := fun a i =>
  O.sum_mem fun c _ => O.mul_mem (hX c i) (hg c a)

theorem continuous_rmul [TopologicalSpace (R ⊗[F] E)] [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous fun X : Fin n → Fin M → R ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul R X g := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  unfold GlobalTheory.CompanionTheory.SW.rmul
  fun_prop

theorem isOpen_tupIn [TopologicalSpace (R ⊗[F] E)] {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsOpen L) :
    IsOpen (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => L := by
    ext X
    simp [tupIn]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hL

end GlobalTheory.CompanionTheory.AvgFree.Shear


open GlobalTheory.CompanionTheory.AvgFree.Shear in
theorem GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n M : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → MeasurePreserving (fun X : (Fin n → Fin M → (Fv F v ⊗[F] E)) => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a)) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O hOc hOo _ n M l a ha hl
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW n M
  have hna : ∀ i, negCol (Fv F v) l a i ∈ O := fun i => by
    by_cases h : i = l
    · simp [negCol, h, O.one_mem]
    · simpa [negCol, h] using O.neg_mem (ha i)
  have hg1 : eMat (Fv F v) l a * eMat (Fv F v) l (negCol (Fv F v) l a) = 1 :=
    eMat_mul_negCol (Fv F v) l a hl
  have hg2 : eMat (Fv F v) l (negCol (Fv F v) l a) * eMat (Fv F v) l a = 1 := by
    have h := eMat_mul_negCol (Fv F v) l (negCol (Fv F v) l a) (negCol_self (Fv F v) l a)
    rwa [negCol_negCol (Fv F v) l a hl] at h
  have hST : ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      GlobalTheory.CompanionTheory.SW.rmul (Fv F v) (GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a))
        (eMat (Fv F v) l (negCol (Fv F v) l a)) = X := fun X => by
    rw [rmul_mul, hg1, rmul_one]
  have hTS : ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      GlobalTheory.CompanionTheory.SW.rmul (Fv F v) (GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l (negCol (Fv F v) l a)))
        (eMat (Fv F v) l a) = X := fun X => by
    rw [rmul_mul, hg2, rmul_one]
  refine measurePreserving_of_compactOpen _ _
    (fun X => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l (negCol (Fv F v) l a)))
    (fun X Y => rmul_add (Fv F v) X Y _) (continuous_rmul (Fv F v) _) (continuous_rmul (Fv F v) _)
    hST hTS (tupIn (Fv F v) (O : Set (Fv F v ⊗[F] E))) (isCompact_tupIn (Fv F v) hOc)
    (isOpen_tupIn (Fv F v) hOo) ⟨0, fun _ _ => O.zero_mem⟩ ?_
  ext X
  constructor
  · intro hX
    have h := rmul_mem (Fv F v) O _ _ (eMat_mem (Fv F v) O l _ hna) hX
    rwa [hST] at h
  · exact rmul_mem (Fv F v) O X _ (eMat_mem (Fv F v) O l a ha)
