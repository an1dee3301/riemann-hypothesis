module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
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
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

universe u

section Topology

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

instance secondCountableTopology_GL_complex : SecondCountableTopology (GL ι ℂ) := by
  have : SecondCountableTopology (Matrix ι ι ℂ) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))
  have : SecondCountableTopology (Matrix ι ι ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

instance secondCountableTopology_archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    SecondCountableTopology (archUnitary h v) := by
  have : SecondCountableTopology (InfinitePlace E → GL ι ℂ) := inferInstance
  exact TopologicalSpace.Subtype.secondCountableTopology _

end Topology

section Groups

variable (G : Type*) [Group G]

def UnfoldOrbit.Statement [MeasurableSpace G] [MeasurableMul G] : Prop :=
  ∀ (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ₀ : Subgroup G) [Countable Γ], Γ₀ ≤ Γ →
    ∀ FD FD₀ : Set G, IsFundamentalDomain Γ FD μ → IsFundamentalDomain Γ₀ FD₀ μ →
    ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ₀, ∀ g, φ (γ * g) = φ g) →
    ∫⁻ g in FD, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ g in FD₀, φ g ∂μ

def DiscreteFundamentalDomain.Statement [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] : Prop :=
  ∀ (μ : Measure G) (Γ : Subgroup G), DiscreteTopology Γ →
    ∃ FD : Set G, MeasurableSet FD ∧ IsFundamentalDomain Γ FD μ

end Groups

section Numbers

variable (E : Type*) [Field E] [NumberField E]

def IdealClassesFinite.Statement : Prop :=
  ∃ T : Set (AddSubgroup E), T.Finite ∧ ∀ I : AddSubgroup E, I.FG → I ≠ ⊥ →
    (∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I) →
    ∃ J ∈ T, ∃ c : E, c ≠ 0 ∧ I = J.map (AddMonoidHom.mulLeft c)

def IntegralFamilyBound.Statement : Prop :=
  ∃ r : ℝ, ∃ a : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
    ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r

end Numbers

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def MajorantExists.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  Nonempty (Majorant h v)

def WittPartner.Statement (h : HermitianForm F E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 → ∃ w₀ : W, h.toSesq x₀ w₀ = 1 ∧ h.toSesq w₀ w₀ = 0

def VectorOrbitsFinite.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (VV : Set W), IsDIntegral h D La → VV ⊆ La →
    (∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) → (∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV) →
    (∃ C : ℕ, ∀ x ∈ VV, lineIndex E La x ≤ C) →
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x

def ArchLatticeDiscrete.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La → DiscreteTopology (archLatticeGroup h v La)

variable (F E)

def CovolumeFiniteBelow (N : ℕ) : Prop :=
  ∀ (W' : Type u) [AddCommGroup W'] [Module E W'] [FiniteDimensional E W']
    (h' : HermitianForm F E W') (n : ℕ) (v' : Basis (Fin n) E W'),
    finrank E W' < N → ArithmeticCovolumeFinite.Statement h' v'

def LatticeOrbitsFiniteBelow (N : ℕ) : Prop :=
  ∀ (W' : Type u) [AddCommGroup W'] [Module E W'] [FiniteDimensional E W']
    (h' : HermitianForm F E W'), finrank E W' < N → LatticeOrbitsFinite.Statement h'

end Spaces

section Inhabitants

open GaussianPlane

abbrev C2 : Type := Multiplicative (ZMod 2)

instance : MeasurableSpace C2 := ⊤

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
