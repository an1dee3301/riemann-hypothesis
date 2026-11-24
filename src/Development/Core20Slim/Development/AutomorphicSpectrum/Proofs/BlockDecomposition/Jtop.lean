module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicGLn
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
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSo

theorem jtop : JTop := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ
  have hcv : Continuous ν := hB.cont

  have hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    have e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x =>
        (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) *
          ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) *
          ((dg ι (Units.map A.i.toMonoidHom δ) : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) := by
      funext x; rw [hJ x]; rfl
    rw [e]
    have h1 : Continuous fun x : cover A ν ι => (x.1.1 : R) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)
  have hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) =
        (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹ := by
      funext x; simp [map_inv]
    rw [e]; exact hval.comp continuous_inv
  have hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
      [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom) := by
    intro S T _ _ _ _ _ φ hφ
    exact Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩
  haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
      x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2) :=
    (continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))
  have hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) := by
    have e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
        x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1} :=
      Set.ext fun x => Iff.rfl
    rw [e]; exact isClosed_singleton.preimage hf
  haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  exact ⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

end GlobalTheory.CompanionTheory.EisSo
