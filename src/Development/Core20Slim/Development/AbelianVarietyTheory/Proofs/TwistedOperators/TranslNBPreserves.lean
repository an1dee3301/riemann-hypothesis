module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.HaarCoords

theorem transl_nB_preserves : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure → lB.IsAddHaarMeasure → lC.IsAddHaarMeasure → SFinite μ → SFinite lB → SFinite lC → ∀ b' : Mx D ρ S₀.rank, ∃ T : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ), MeasurePreserving T (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) ∧ ∀ p, d.levi (T p).1.1 * (d.nB (T p).2.1 * d.nC (T p).2.2) = d.nB b' * (d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d μ lB lC hμ hB hC _ _ _ b'
  obtain ⟨hTR, _, _, hSC, hBor⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI := hμ; haveI := hB; haveI := hC; haveI := hTR; haveI := hSC; haveI := hBor
  haveI hMxB : ∀ m n : ℕ, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  haveI hMxS : ∀ m n : ℕ, SecondCountableTopology (Mx D m n) := fun m n =>
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩

  let v : UX D ρ → Mx D ρ S₀.rank := fun u => ((u.1)⁻¹ : GL (Fin ρ) (AE D)).1 ⬝ b'
  refine ⟨fun p => (p.1, (v p.1 + p.2.1, cComm S₀ (v p.1) p.2.1 + p.2.2)), ?_, ?_⟩
  · have hvm : Measurable v := by
      have hinv : Continuous fun u : UX D ρ => (((u.1)⁻¹ : GL (Fin ρ) (AE D)) : Matrix (Fin ρ) (Fin ρ) (AE D)) :=
        Units.continuous_coe_inv.comp continuous_subtype_val
      exact (hinv.matrix_mul continuous_const).measurable

    have hplus : Continuous fun b : Mx D ρ S₀.rank => plus S₀ b := by
      show Continuous fun b : Mx D ρ S₀.rank => giA S₀ ⬝ adj b
      exact continuous_const.matrix_mul continuous_adj
    have hΦ : Measurable fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => ((cComm S₀ q.1 q.2 : skewA D ρ) : Mx D ρ ρ) := by
      have h1 : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => q.2 ⬝ plus S₀ q.1 :=
        continuous_snd.matrix_mul (hplus.comp continuous_fst)
      have h2 : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank => q.1 ⬝ plus S₀ q.2 :=
        continuous_fst.matrix_mul (hplus.comp continuous_snd)
      have hc : Continuous fun q : Mx D ρ S₀.rank × Mx D ρ S₀.rank =>
          half D • (q.2 ⬝ plus S₀ q.1 - q.1 ⬝ plus S₀ q.2) :=
        (continuous_const_smul (half D)).comp (h1.sub h2)
      exact hc.measurable
    have hg : Measurable fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) =>
        ((v p.1 + p.2.1, cComm S₀ (v p.1) p.2.1 + p.2.2) : Mx D ρ S₀.rank × skewA D ρ) := by
      refine ((hvm.comp measurable_fst).add (measurable_fst.comp measurable_snd)).prodMk ?_
      exact Measurable.subtype_mk (f := fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) =>
          ((cComm S₀ (v p.1) p.2.1 : skewA D ρ) : Mx D ρ ρ) + (p.2.2 : Mx D ρ ρ))
        (h := fun p => (cComm S₀ (v p.1) p.2.1 + p.2.2).2)
        ((hΦ.comp ((hvm.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).add
          (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)))
    have hfib : ∀ u : UX D ρ, Measure.map (fun q : Mx D ρ S₀.rank × skewA D ρ =>
        ((v u + q.1, cComm S₀ (v u) q.1 + q.2) : Mx D ρ S₀.rank × skewA D ρ)) (lB.prod lC) = lB.prod lC := by
      intro u
      have hk : Measurable fun q : Mx D ρ S₀.rank × skewA D ρ => (cComm S₀ (v u) q.1 + q.2 : skewA D ρ) :=
        Measurable.subtype_mk (f := fun q : Mx D ρ S₀.rank × skewA D ρ =>
            ((cComm S₀ (v u) q.1 : skewA D ρ) : Mx D ρ ρ) + (q.2 : Mx D ρ ρ))
          (h := fun q => (cComm S₀ (v u) q.1 + q.2).2)
          ((hΦ.comp (measurable_const.prodMk measurable_fst)).add (measurable_subtype_coe.comp measurable_snd))
      exact ((measurePreserving_add_left lB (v u)).skew_product (g := fun b (c : skewA D ρ) => cComm S₀ (v u) b + c) hk
        (Filter.Eventually.of_forall fun b => map_add_left_eq_self lC _)).map_eq
    exact (MeasurePreserving.id μ).skew_product
      (g := fun (u : UX D ρ) (q : Mx D ρ S₀.rank × skewA D ρ) => ((v u + q.1, cComm S₀ (v u) q.1 + q.2) : Mx D ρ S₀.rank × skewA D ρ))
      hg (Filter.Eventually.of_forall hfib)
  · rintro ⟨u, b, c⟩
    show d.levi u.1 * (d.nB (v u + b) * d.nC (cComm S₀ (v u) b + c)) = d.nB b' * (d.levi u.1 * (d.nB b * d.nC c))
    have hv : u.1.1 ⬝ v u = b' := by
      show u.1.1 ⬝ (((u.1)⁻¹ : GL (Fin ρ) (AE D)).1 ⬝ b') = b'
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [d.nC_add, ← mul_assoc (d.nB _), ← d.nB_mul_nB, ← mul_assoc, ← mul_assoc, d.levi_mul_nB, hv, mul_assoc, mul_assoc]

end GlobalTheory.HaarCoords
