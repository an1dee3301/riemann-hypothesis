module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled.Tr

abbrev UD (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) : Type := (adCM D.sp.cm.sig χ).U (-1) (Fin n)

def TStd : Prop := Dict → DictInf →
  ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), ∃ Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n,
    (∀ g, g ∈ GlobalTheory.StdUnn.GF D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uΓ (-1) (Fin n)) ∧
    (∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n))) ∧
    (∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin n)) ∧
    ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Ψ g).1 = Matrix.GeneralLinearGroup.det a

def Chart : Prop :=
  ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a →
    ∃ (Φ : GA D (dblSp V) ≃ₜ* UD D χ V.rank) (p : siegel V),
    (∀ g, g ∈ GQ (dblSp V) ↔ Φ g ∈ (adCM D.sp.cm.sig χ).uΓ (-1) (Fin V.rank)) ∧
    (∀ g, g ∈ siegel V ↔ Φ g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin V.rank))) ∧
    (∀ k, k ∈ Khat V a ↔ Φ ((p : GA D (dblSp V))⁻¹ * k * p) ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin V.rank)) ∧
    (∀ q : siegel V, bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) (Φ q).1 = aP V q) ∧
    ∀ x : (AE D)ˣ, (adCM D.sp.cm.sig χ).lg x = Real.log (absA D x)

def TChart : Prop := Dict → DictInf → TStd → Chart

def Scal : Prop :=
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [T2Space G'] [LocallyCompactSpace G'] (Φ : G ≃ₜ* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (η : G' → ℝ)
    (N : ℝ), IsCompact (K' : Set G') → IsPar Γ' K' P' c → IsHt Γ' K' P' η → (∀ g, g ∈ Γ ↔ Φ g ∈ Γ') → (∀ g, g ∈ P ↔ Φ g ∈ P') →
    (AllRep K' fun ρ => HasWall Γ' K' P' P' c η η (fun g => N * η g) ρ) →
    ∀ f : G → ℂ, Continuous f → (∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Φ.symm k))) →
      ∃ (A : ℂ → ℂ) (H : ℂ → G → ℂ) (R : ℝ), Differentiable ℂ A ∧ (∃ z, A z ≠ 0) ∧ (∀ g, Differentiable ℂ (H · g)) ∧
        Continuous (fun y : ℂ × G => H y.1 y.2) ∧
        (∀ z : ℂ, R < z.re → ∀ g, H z g = A z * GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g) ∧
        ∀ a b : ℝ, R < a → b < -R → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g,
          ‖H z g‖ ≤ M * (‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp (a * η (Φ x)) : ℂ)) g‖ +
            ‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp ((N - b) * η (Φ x)) : ℂ)) g‖)

def TScal : Prop := SecLaw → WallLaw → Scal



end ResidueKilled.Tr

end
