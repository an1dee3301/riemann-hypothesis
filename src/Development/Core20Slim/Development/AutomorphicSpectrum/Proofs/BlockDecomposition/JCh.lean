module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionMeasure
public import GroundTheory.GlobalFields.Adele.Approximation
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Topology
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisSo

theorem jCh : StdGood → BdetLaw → JTop → JCh := by
  intro hS hB _ F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hBase hi hJ
  have hL : (adStd F).GoodL := hS F
  obtain ⟨-, -, -, -, hk, hd⟩ := hB F 𝔸[F] (adStd F) hL (ι ⊕ ι) Set.univ
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) := by
    have h := Continuous.units_map (Matrix.detMonoidHom (n := ι ⊕ ι) (R := 𝔸[F]))
      (Continuous.matrix_det continuous_id)
    convert h using 1
    funext x
    apply Units.ext
    rfl
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hfst : Continuous fun x : cover A ν ι => x.1.1 := continuous_fst.comp continuous_subtype_val
  have hadd : ∀ p g : cover A ν ι, ld (p * g) = ld p + ld g := by
    intro p g
    simp only [ld, map_mul]
    exact hL.lgmul _ _
  have hK : ∀ k ∈ cK α j, ld k = 0 := by
    intro k hk'
    obtain ⟨κ, hκ, he⟩ := hk'.2
    have hdk : Matrix.GeneralLinearGroup.det (prj A ν ι k) = Matrix.GeneralLinearGroup.det κ := by
      rw [← he]
      simp [MulAut.conj_apply, map_mul, map_inv, mul_comm]
    have := hk κ (by intro r hr; exact absurd (Set.mem_univ r) hr) hκ
    rw [hd] at this
    simp only [ld, hdk]
    exact this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p _ q _
    simp [c0]
  · intro p _
    exact Circle.norm_coe _
  · intro γ hγ _
    obtain ⟨⟨x, hx⟩, -⟩ := hγ
    have := hG.toGoodL.χi x
    simp only [c0]
    have hx' : Units.map A.i.toMonoidHom x = γ.1.1 := hx
    rw [← hx', this]
    simp
  · exact (continuous_subtype_val.comp (hG.toGoodL.χcont.comp hfst)).continuousOn
  · intro p _ g
    exact hadd p g
  · intro g k hk'
    rw [hadd, hK k hk', add_zero]
  · intro γ hγ _
    obtain ⟨-, ⟨g, hg⟩⟩ := hγ
    have e : Matrix.GeneralLinearGroup.det (prj A ν ι γ) = Units.map (adStd F).i.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
      have hg' : Matrix.GeneralLinearGroup.map (adStd F).i g = γ.1.2 := hg
      show Matrix.GeneralLinearGroup.det γ.1.2 = _
      rw [← hg']
      apply Units.ext
      show ((Matrix.GeneralLinearGroup.map (adStd F).i g : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).det =
        (adStd F).i (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).det
      rw [RingHom.map_det]
      rfl
    simp only [ld, e]
    exact hL.lgi _
  · exact hL.lgcont.comp (hdet.comp hprj)

end GlobalTheory.CompanionTheory.EisSo
