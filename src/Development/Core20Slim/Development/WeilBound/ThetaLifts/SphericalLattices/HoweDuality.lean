module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.UnrAtDiv
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.LocDataV
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.LocDataVAlt
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.GenOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem howeInert : HoweInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he
  obtain ⟨⟨w, hin⟩, hvT⟩ := inert_ctx hT he
  have ha : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.α u :=
    fun u hu => hT.chars.unrα u fun h => hvT (hu ▸ h)
  have hb : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.β u :=
    fun u hu => hT.chars.unrβ u fun h => hvT (hu ▸ h)
  refine ⟨fun ω ρ hL => ?_, fun ω ρ hL => ?_⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hb
      (fun u hu => unrAt_div (hb u hu) (ha u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' ha
      (fun u hu => unrAt_div (ha u hu) (hb u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV' hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩

end PositivityTheory.Sph

end
