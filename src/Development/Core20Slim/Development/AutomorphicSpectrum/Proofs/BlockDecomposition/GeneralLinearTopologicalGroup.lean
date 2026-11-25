module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.RgEisTop

section Units

variable {M : Type} [TopologicalSpace M] [Monoid M] [ContinuousMul M] [T2Space M]

theorem isClosedEmbedding_embedProduct : IsClosedEmbedding (Units.embedProduct M) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hr : Set.range (Units.embedProduct M) =
      {p : M × Mᵐᵒᵖ | p.1 * MulOpposite.unop p.2 = 1} ∩
        {p : M × Mᵐᵒᵖ | MulOpposite.unop p.2 * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, hu⟩
      have h1 : (u : M) = x := congrArg Prod.fst hu
      have h2 : MulOpposite.op ((u⁻¹ : Mˣ) : M) = y := congrArg Prod.snd hu
      subst h1 h2
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, MulOpposite.unop y, h1, h2⟩, rfl⟩
  rw [hr]
  have hu : Continuous fun p : M × Mᵐᵒᵖ => MulOpposite.unop p.2 :=
    MulOpposite.continuous_unop.comp continuous_snd
  exact (isClosed_eq (continuous_fst.mul hu) continuous_const).inter
    (isClosed_eq (hu.mul continuous_fst) continuous_const)

end Units

section Mat

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem generalLinear_t2Space [T2Space R] : T2Space (GL ι R) :=
  (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.t2Space

theorem gl_locallyCompact [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL ι R) := by
  have : LocallyCompactSpace (Matrix ι ι R) := inferInstanceAs (LocallyCompactSpace (ι → ι → R))
  have : LocallyCompactSpace (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isClosedEmbedding.locallyCompactSpace
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).locallyCompactSpace

theorem gl_secondCountable [T2Space R] [SecondCountableTopology R] :
    SecondCountableTopology (GL ι R) := by
  have : SecondCountableTopology (Matrix ι ι R) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → R))
  have : SecondCountableTopology (Matrix ι ι R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι R)).symm.isEmbedding.secondCountableTopology
  exact (isClosedEmbedding_embedProduct (M := Matrix ι ι R)).isEmbedding.secondCountableTopology

end Mat

open PositivityTheory.RgEis

theorem isClosed_uSub {E R : Type} [Field E] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (A : Ad E R) (hσ : Continuous A.σ) (ε : ℤˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    IsClosed (A.uSub ε ι : Set (GL (ι ⊕ ι) R)) := by
  have hv : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    Units.continuous_val
  have hm : Continuous fun g : GL (ι ⊕ ι) R => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ :=
    hv.matrix_map hσ
  exact isClosed_eq ((hv.matrix_transpose.mul continuous_const).mul hm) continuous_const

theorem grpTop : PositivityTheory.RgEis.GrpTop := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ ε
  have hc := isClosed_uSub A hA.σcont ε ι
  have hce : IsClosedEmbedding (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) :=
    hc.isClosedEmbedding_subtypeVal
  have := generalLinear_t2Space R (ι ⊕ ι)
  have := gl_locallyCompact R (ι ⊕ ι)
  have := gl_secondCountable R (ι ⊕ ι)
  refine ⟨generalLinear_t2Space R ι, gl_locallyCompact R ι, gl_secondCountable R ι, hce.isEmbedding.t2Space,
    hce.locallyCompactSpace, hce.isEmbedding.secondCountableTopology, ?_⟩
  exact hce.isCompact_preimage (hA.toGoodL.kcpt (ι ⊕ ι))

end GlobalTheory.CompanionTheory.RgEisTop
