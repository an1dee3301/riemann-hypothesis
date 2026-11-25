module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_unitary_semisimple : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  first | exact @GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | exact GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | (intros; apply GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl <;> assumption)
