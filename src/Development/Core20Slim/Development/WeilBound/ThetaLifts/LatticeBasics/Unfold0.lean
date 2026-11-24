module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def Law (χ : Chr F E) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x

variable {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}







end GlobalTheory.ThK.Dbl

end
