module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixFinite
public import GroundTheory.GlobalFields.Adele.Approximation
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.IntegersLattice
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Topology
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ConductorIdeal
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RgEisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

theorem zetaIntegrand_tensor {k : Type} [Field k] [NumberField k]
    (φ : 𝓢(Unit → mixedSpace k, ℂ)) (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ) (x : IdeleGroup k) :
    GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s =
      (rd φ (fun _ => ((toInfinite k x : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k)) *
          (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) *
          ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s) *
        (g (fun _ => ((toFinite k x : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k)) *
          (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
          ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (ω.toIdele x : ℂ) = (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
      (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule k x : ℝ) : ℂ) ^ s =
      ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s *
        ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s := by
    have h : (ideleModule k x : ℝ) = (ideleModule k (ofInfinite (toInfinite k x)) : ℝ) *
        (ideleModule k (ofFinite (toFinite k x)) : ℝ) := by
      conv_lhs => rw [← ofFinite_mul_ofInfinite x, map_mul]
      rw [mul_comm]
      rfl
    rw [h, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ideleModule k _).2.le
      (ideleModule k _).2.le]
  rw [hchi, hmod]
  change φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * g (fun _ => (x : 𝔸[k]).2) * _ * _ = _
  change _ = (φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * _ * _) *
    (g (fun _ => (x : 𝔸[k]).2) * _ * _)
  ring

theorem zSplit : ZSplit := by
  intro k _ _ φ g ω s _
  set A : (InfiniteAdeleRing k)ˣ → ℂ := fun a =>
    rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
      ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ s with hA
  set B : (FiniteAdeleRing (𝓞 k) k)ˣ → ℂ := fun b =>
    g (fun _ => (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
      ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup k,
      GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s = (fun p => A p.1 * B p.2) (IdeleGroup.prodEquiv k x) :=
    zetaIntegrand_tensor φ g ω s
  have hemb : MeasurableEmbedding (IdeleGroup.prodEquiv k) :=
    (IdeleGroup.prodEquiv k).toHomeomorph.measurableEmbedding
  unfold globalZeta zInf zFin
  simp_rw [hF]
  rw [(measurePreserving_prodEquiv (K := k)).integral_comp hemb (fun p => A p.1 * B p.2)]
  exact integral_prod_mul A B

end GlobalTheory.CompanionTheory.RgEisTF
