module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Lattice
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalAtPlace
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
public import Development.Core20Slim.GroundTheory.AutomorphicForms.UnitaryGroupScheme
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology

noncomputable section

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def vecCoordsHomeomorph : (ι → R ⊗[K] E) ≃ₜ (ι → κ → R) :=
  Homeomorph.piCongrRight fun _ => tensorCoordsHomeomorph R b

theorem stdLattice_eq_preimage (O : Subring R) :
    stdLattice ι R b O = vecCoordsHomeomorph R b ⁻¹'
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set R) := by
  ext x
  simp only [stdLattice, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies, SetLike.mem_coe]
  rfl

theorem isOpen_stdLattice {O : Subring R} (hO : IsOpen (O : Set R)) :
    IsOpen (stdLattice ι R b O) := by
  rw [stdLattice_eq_preimage]
  exact (vecCoordsHomeomorph R b).continuous.isOpen_preimage _
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO)

theorem isCompact_stdLattice {O : Subring R} (hO : IsCompact (O : Set R)) :
    IsCompact (stdLattice ι R b O) := by
  rw [stdLattice_eq_preimage]
  exact (vecCoordsHomeomorph R b).isCompact_preimage.2
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO)

theorem continuous_unitaryMat_mulVec :
    Continuous fun p : unitaryPoints K E H R × (ι → R ⊗[K] E) => unitaryMat p.1 *ᵥ p.2 := by
  have h1 : Continuous fun p : unitaryPoints K E H R × (ι → R ⊗[K] E) => unitaryMat p.1 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
  exact h1.matrix_mulVec continuous_snd

section NumberField

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E] {H : Matrix ι ι E} (b : Basis κ K E)
  (v : HeightOneSpectrum (𝓞 K))

end NumberField

end

end GroundTheory.Automorphic
