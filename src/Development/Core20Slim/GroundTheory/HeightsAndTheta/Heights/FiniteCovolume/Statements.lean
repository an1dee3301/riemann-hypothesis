module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.UnitaryGroupScheme
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LatticeOrbitsFinite.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ S : Set (AddSubgroup W), S.Finite ∧
    ∀ La : AddSubgroup W, IsDIntegral h D La → ∃ L ∈ S, ∃ g : h.unitaryGroup, g • L = La

def LinePairOrbitsFinite.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ S : Set (AddSubgroup W × Submodule E W), S.Finite ∧
    ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
      ∃ p ∈ S, ∃ g : h.unitaryGroup,
        g • p.1 = La ∧ p.2.map ((g : W ≃ₗ[E] W) : W →ₗ[E] W) = l

def ArithmeticCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ) (La : AddSubgroup W),
    IsDIntegral h D La → ∃ FD : Set (archUnitary h v),
      IsFundamentalDomain (archLatticeGroup h v La) FD μ ∧ μ FD < ⊤

instance measurableSpace_unitaryPoints_adele (H : Matrix ι ι E) :
    MeasurableSpace (unitaryPoints F E H 𝔸[F]) :=
  borel _

instance borelSpace_unitaryPoints_adele (H : Matrix ι ι E) :
    BorelSpace (unitaryPoints F E H 𝔸[F]) :=
  ⟨rfl⟩

def AdelicCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (unitaryPoints F E (gram h.toSesq v) 𝔸[F])) [μ.IsHaarMeasure],
    ∃ FD : Set (unitaryPoints F E (gram h.toSesq v) 𝔸[F]),
      IsFundamentalDomain (hermitianDiagonal h v).range FD μ ∧ μ FD < ⊤

def ScalingLaw.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ)
    (La : AddSubgroup W) (VV : Set W),
    IsDIntegral h D La → VV ⊆ La → (∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) →
    (∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV) →
    (∃ C : ℕ, ∀ x ∈ VV, lineIndex E La x ≤ C) →
    ∃ FD : Set (archUnitary h v), IsFundamentalDomain (archLatticeGroup h v La) FD μ ∧
      ∀ t : ℝ, 0 < t → massBelow M μ FD VV t < ⊤ ∧
        ∀ θ : ℝ, 0 < θ → massBelow M μ FD VV (θ * t) =
          ENNReal.ofReal (θ ^ (2 * finrank ℚ F * (finrank E W - 1))) * massBelow M μ FD VV t

def MahlerCompactness.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (D : ℕ) (t : ℝ), 0 < t →
    ∃ S : Set (AddSubgroup W), S.Finite ∧ ∃ K : Set (archUnitary h v), IsCompact K ∧
      ∀ (La : AddSubgroup W) (g : archUnitary h v), IsDIntegral h D La →
        (∀ x ∈ La, x ≠ 0 → t ≤ M.len (invApply g (vecAt v x))) →
        ∃ γ : h.unitaryGroup, γ • La ∈ S ∧ archEmbed h v γ * g ∈ K

def ShortVectorIsotropic.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (D : ℕ) (La : AddSubgroup W) (g : archUnitary h v) (x : W),
    IsDIntegral h D La → x ∈ La → M.len (invApply g (vecAt v x)) < 1 → h.toSesq x x = 0

def ShortestVectorIndex.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (r : ℝ),
    (∃ a : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r) →
    ∀ (D : ℕ) (La : AddSubgroup W) (g : archUnitary h v) (x : W),
      IsDIntegral h D La → x ∈ La → x ≠ 0 →
      (∀ y ∈ La, y ≠ 0 → M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y))) →
      (lineIndex E La x : ℝ) ≤ (r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)

def UnfoldingIntegral.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ)
    (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∃ FD : Set (archUnitary h v), IsFundamentalDomain (vecStabGroup h v La x₀) FD μ ∧
      ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ t : ℝ, 0 < t →
        μ (FD ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) =
          C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1)))

def ParabolicDecomposition.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (x₀ : W), x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∀ g : archUnitary h v, ∃ p k : archUnitary h v, k ∈ M.stab ∧ g = p * k ∧
      ∀ w, ∃ c : ℂ, (((p : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) =
        c • vecAt v x₀ w

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
