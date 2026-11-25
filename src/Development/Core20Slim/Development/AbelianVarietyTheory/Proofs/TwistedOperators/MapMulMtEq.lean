module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHermNDInvTranspose
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.RowMat

theorem map_coord_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (f : V → V) (hf : Measurable f)
    (hfH : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map f = μ) (ρ : ℕ)
    [inst : MeasurableSpace (Fin ρ → V)] [hB : BorelSpace (Fin ρ → V)]
    (lam : Measure (Fin ρ → V)) [hlam : lam.IsAddHaarMeasure] :
    lam.map (fun b i => f (b i)) = lam := by
  have e : inst = MeasurableSpace.pi :=
    hB.measurable_eq.trans (@BorelSpace.measurable_eq (Fin ρ → V) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have hp : MeasurePreserving f (Measure.addHaar : Measure V) Measure.addHaar :=
    ⟨hf, hfH _ inferInstance⟩
  have hpi := measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)
  rw [Measure.isAddLeftInvariant_eq_smul lam (Measure.pi fun _ : Fin ρ => (Measure.addHaar : Measure V)),
    Measure.map_smul _ hpi.measurable.aemeasurable]
  congr 1
  exact (measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)).map_eq

theorem map_mul_mt_eq : ∀ (D : D7) (S₀ : HSp D) (ρ : ℕ) (lam : Measure (Mx D ρ S₀.rank)),
    lam.IsAddHaarMeasure → ∀ h : GA D S₀,
      lam.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) = lam := by
  intro D S₀ ρ lam hlam h
  have h1 : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  have h2 : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have h3 : LocallyCompactSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.1
  have h4 : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  have h5 : BorelSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.2
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hrow := GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm.1 S₀.rank S₀.gram
    (hcm.2 S₀) h
  have e : (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) =
      fun b i => Matrix.vecMul (b i) (mt S₀ h) := by
    funext b i j
    rfl
  rw [e]
  have hm : Measurable (fun x : Fin S₀.rank → AE D => Matrix.vecMul x (mt S₀ h)) :=
    (Continuous.matrix_vecMul continuous_id continuous_const).measurable
  exact map_coord_eq (V := Fin S₀.rank → AE D) (f := fun x => Matrix.vecMul x (mt S₀ h)) (hf := hm)
    (hfH := fun μ hμ => hrow μ hμ) (ρ := ρ) (inst := measMx ρ S₀.rank)
    (hB := @BorelSpace.mk _ _ (measMx ρ S₀.rank) rfl) (lam := lam) (hlam := hlam)

end GlobalTheory.AdelicModulus.RowMat
