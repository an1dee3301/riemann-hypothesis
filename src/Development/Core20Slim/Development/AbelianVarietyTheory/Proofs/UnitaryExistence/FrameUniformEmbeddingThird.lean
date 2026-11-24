module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem coset_fv_mulVec (A : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (A.map (inclR (F := F) (Af F))) *ᵥ AdLat.fv F x = AdLat.fv F (A *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) A x i).symm

theorem coset_tmul_eq (t : Af F) (x : Fin n → E) :
    (fun i => t ⊗ₜ[F] x i : Fin n → AdLat.RA F E) = (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • AdLat.fv F x := by
  funext i
  simp only [AdLat.fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem coset_smul_mem_hat (L : Set (Fin n → E)) (t : Af F) (ht : ∀ v, t v ∈ v.adicCompletionIntegers F)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨t * s, fun v => mul_mem (ht v) (hs v), x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem coset_mulVec_mem_hat (L : Set (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hA : ∀ x ∈ L, A *ᵥ x ∈ L)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (A.map (inclR (F := F) (Af F))) *ᵥ w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    rw [coset_tmul_eq, Matrix.mulVec_smul, coset_fv_mulVec]
    exact coset_smul_mem_hat L s hs _ (AdLat.Half.fv_mem_hat' L _ (hA x hx))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [Matrix.mulVec_add]; exact add_mem h h'
  | neg w _ h => rw [Matrix.mulVec_neg]; exact neg_mem h

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



end GlobalTheory.RecDict
