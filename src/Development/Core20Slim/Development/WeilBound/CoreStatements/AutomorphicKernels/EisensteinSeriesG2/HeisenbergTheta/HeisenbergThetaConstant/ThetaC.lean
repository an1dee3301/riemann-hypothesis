module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.TateMain
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing

namespace PositivityTheory.He2M1

open GroundTheory.Global GroundTheory.Automorphic IdeleGroup PositivityTheory.RgEis

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) : (ι → 𝔸[k]) → ℂ :=
  fun x ↦ F ((A : Matrix ι ι 𝔸[k]) *ᵥ x)

noncomputable def thetaC (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) : ℂ :=
  ∑' ξ : ι → k, F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)

noncomputable def scalC (a : IdeleGroup k) : GL ι 𝔸[k] :=
  Units.map (Matrix.scalar ι : 𝔸[k] →+* Matrix ι ι 𝔸[k]).toMonoidHom a

noncomputable def thetaCInt (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ u in normOneFundamentalDomain k,
    thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ)
      ∂normOneMeasure k

noncomputable def thetaCFun (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (x : ℝ) : ℂ :=
  if hx : 0 < x then thetaCInt w F ω ⟨x, hx⟩ else 0

noncomputable def volChar (ω : HeckeCharacter k) : ℂ :=
  ∫ u in normOneFundamentalDomain k, (ω.toIdele (u : IdeleGroup k) : ℂ) ∂normOneMeasure k

noncomputable def thetaCConst (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) : ℂ :=
  F 0 * volChar ω

end PositivityTheory.He2M1
