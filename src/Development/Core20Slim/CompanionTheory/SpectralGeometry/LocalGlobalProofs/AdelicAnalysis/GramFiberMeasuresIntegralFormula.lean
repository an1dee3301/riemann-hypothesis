module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarModularCharacterOfContinuousActionStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentitiesStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
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
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Basic
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
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ScaleCont

section Actions

variable {K : Type} [CommRing K] {n M : ℕ}

def tupR (X : Fin n → Fin M → K) (g : Matrix (Fin n) (Fin n) K) : Fin n → Fin M → K :=
  fun a i => ∑ c, X c i * g c a

theorem tupR_tupR (X : Fin n → Fin M → K) (g h : Matrix (Fin n) (Fin n) K) :
    tupR (tupR X g) h = tupR X (g * h) := by
  funext a i
  simp only [tupR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

theorem tupR_one (X : Fin n → Fin M → K) : tupR X 1 = X := by
  funext a i
  simp [tupR, Matrix.one_apply]

def tupAction : DistribMulAction (GL (Fin n) K) (Fin n → Fin M → K) where
  smul q X := tupR X ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  one_smul X := by
    show tupR X (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = X
    simp [tupR_one]
  mul_smul q q' X := by
    show tupR X (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tupR (tupR X ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [tupR_tupR, mul_inv_rev, Units.val_mul]
  smul_zero q := by
    show tupR 0 _ = 0
    funext a i
    simp [tupR]
  smul_add q X Y := by
    show tupR (X + Y) _ = tupR X _ + tupR Y _
    funext a i
    simp [tupR, add_mul, Finset.sum_add_distrib]

theorem cT_one' (s : K →+* K) : cT s (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [cT, Matrix.map_one]

theorem cT_mul' (s : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

def hermAction (s : K →+* K) (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    DistribMulAction (GL (Fin n) K) H where
  smul q S := ⟨cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hmem S _⟩
  one_smul S := by
    apply Subtype.ext
    show cT s (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = S
    simp [cT_one']
  mul_smul q q' S := by
    apply Subtype.ext
    show cT s (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (S : Matrix (Fin n) (Fin n) K) * (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (cT s ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (S : Matrix (Fin n) (Fin n) K) * ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [mul_inv_rev, Units.val_mul, cT_mul']
    simp only [Matrix.mul_assoc]
  smul_zero q := by
    apply Subtype.ext
    show cT s _ * ((0 : H) : Matrix (Fin n) (Fin n) K) * _ = 0
    simp
  smul_add q S T := by
    apply Subtype.ext
    show cT s _ * ((S + T : H) : Matrix (Fin n) (Fin n) K) * _ =
      cT s _ * (S : Matrix (Fin n) (Fin n) K) * _ + cT s _ * (T : Matrix (Fin n) (Fin n) K) * _
    simp [Matrix.mul_add, Matrix.add_mul]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_inv_val :
    Continuous fun q : GL (Fin n) K => ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  Units.continuous_val.comp continuous_inv

theorem tup_continuousSMul :
    @ContinuousSMul (GL (Fin n) K) (Fin n → Fin M → K) (tupAction (K := K)).toSMul _ _ := by
  letI := tupAction (K := K) (n := n) (M := M)
  refine ⟨?_⟩
  show Continuous fun p : GL (Fin n) K × (Fin n → Fin M → K) =>
    tupR p.2 ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [tupR]
  refine continuous_finsetSum _ fun c _ => ?_
  refine Continuous.mul ?_ ?_
  · exact (continuous_apply i).comp ((continuous_apply c).comp continuous_snd)
  · exact (continuous_apply a).comp ((continuous_apply c).comp (continuous_inv_val.comp continuous_fst))

theorem herm_continuousSMul (s : K →+* K) (hs : Continuous s)
    (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    @ContinuousSMul (GL (Fin n) K) H (hermAction s H hmem).toSMul _ _ := by
  letI := hermAction s H hmem
  refine ⟨?_⟩
  have hq : Continuous fun p : GL (Fin n) K × H =>
      ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := continuous_inv_val.comp continuous_fst
  have hS : Continuous fun p : GL (Fin n) K × H => (p.2 : Matrix (Fin n) (Fin n) K) :=
    continuous_subtype_val.comp continuous_snd
  have hc : Continuous fun p : GL (Fin n) K × H =>
      cT s ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp only [cT]
    exact (hq.matrix_map hs).matrix_transpose
  exact ((hc.matrix_mul hS).matrix_mul hq).subtype_mk _

end Actions

theorem fibre_scale_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∃ κ : GL (Fin n) (R ⊗[F] E) → ℝ≥0, Continuous κ ∧ (∀ g, κ g ≠ 0) ∧ κ 1 = 1 ∧ ∀ (g : GL (Fin n) (R ⊗[F] E)) (S S' : HermR R σ n), (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → m S' = κ g • (m S).map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm
  obtain ⟨r1, r2, r3, r4, -⟩ := id hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := k8 n M
  have hmem := (GlobalTheory.T.gram_right_action_identities F E σ hCM M J hJ R n).2.2.2.1
  letI a1 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tupAction
  haveI c1 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tup_continuousSMul
  obtain ⟨χ₁, hχ₁c, hχ₁⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (Fin n → Fin M → R ⊗[F] E) μ (GL (Fin n) (R ⊗[F] E))
  letI a2 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    hermAction (sigR R σ) (HermR R σ n) hmem
  haveI c2 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    herm_continuousSMul (sigR R σ) k5 (HermR R σ n) hmem
  obtain ⟨χ₂, hχ₂c, hχ₂⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (HermR R σ n) ν (GL (Fin n) (R ⊗[F] E))
  have hne : ∀ (χ : GL (Fin n) (R ⊗[F] E) →* ℝ≥0) (g), χ g ≠ 0 := by
    intro χ g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  refine ⟨fun g => χ₁ g * χ₂ g⁻¹, hχ₁c.mul (hχ₂c.comp continuous_inv), ?_, ?_, ?_⟩
  · exact fun g => mul_ne_zero (hne χ₁ g) (hne χ₂ g⁻¹)
  · simp
  · intro g S S' hS'
    let τ : HermR R σ n → HermR R σ n := fun S => g⁻¹ • S
    have hτ : ∀ S : HermR R σ n, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
          (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
      intro S
      show cT (sigR R σ) (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
        (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
      rw [inv_inv]
    have hS'τ : S' = τ S := Subtype.ext (hS'.trans (hτ S).symm)
    have hmap₁ : μ.map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = χ₁ g⁻¹ • μ := by
      have := hχ₁ g⁻¹
      have e : (fun v : Fin n → Fin M → R ⊗[F] E => g⁻¹ • v) =
          fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
        funext X
        show tupR X (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
        rw [inv_inv]
        rfl
      rwa [e] at this
    have hmap₂ : ν.map τ = χ₂ g⁻¹ • ν := hχ₂ g⁻¹
    have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hCM M J hJ R hR n μ ν m hμ hν hm
      (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Matrix.isUnits_det_units g) τ hτ
      (χ₁ g⁻¹) (χ₂ g⁻¹) hmap₁ hmap₂ S
    rw [hS'τ]
    have hinv : χ₁ g * χ₁ g⁻¹ = 1 := by rw [← map_mul]; simp
    calc m (τ S) = (χ₁ g * χ₁ g⁻¹) • m (τ S) := by rw [hinv, one_smul]
      _ = χ₁ g • (χ₁ g⁻¹ • m (τ S)) := by rw [mul_smul]
      _ = χ₁ g • (χ₂ g⁻¹ • (m S).map fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
        rw [key]
      _ = _ := by rw [mul_smul]

end GlobalTheory.CompanionTheory.SW.ScaleCont
