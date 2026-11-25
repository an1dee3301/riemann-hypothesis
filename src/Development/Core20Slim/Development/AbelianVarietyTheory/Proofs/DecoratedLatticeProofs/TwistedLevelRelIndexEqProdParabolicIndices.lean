module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemBlockUpperTriangularTwoIffLowerLeftZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Setoid.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto 
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.TwistIndex

open Classical

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (g : GL (Fin n) κ) : Formalism.L2.DIV.upperLeftBlock (le_refl n) g = g := by
  have hg : g ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 n) : Subgroup (GL (Fin n) κ)) := by
    show (g : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix _ hg]
  ext i j
  simp [Fin.castLE]

variable {D : D7}

theorem mem_datY_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr hr' : r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x : GL (Fin V.rank) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ↔
      x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr' Pg ∅ (LevelP.triv _ _ _) χ' ξ' Lev.Frm.B) ∧
        ∀ PP ∈ Q, Formalism.L2.DIV.redFn β PP x ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))) := by
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩, fun PP hP => ?_⟩
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
    · exact (Formalism.L2.DIV.mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 PP) hP)).2
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩
    exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨h2, h6 PP hP⟩


end GlobalTheory.TwistIndex

end
