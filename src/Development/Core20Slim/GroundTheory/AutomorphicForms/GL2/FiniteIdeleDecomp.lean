module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import GroundTheory.LocalFields.LocalFourier
public import GroundTheory.LocalFields.LocalFourierHaar
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology GroundTheory.Global GroundTheory.LocalField
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise

namespace GroundTheory.Automorphic.GodementSection

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

instance measurableSpace_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel _

instance borelSpace_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

def finUnitAt (v : HeightOneSpectrum (𝓞 K)) : (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)







section Units

variable (v : HeightOneSpectrum (𝓞 K))





end Units

section AtS

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def finUnitsAt : (FiniteAdeleRing (𝓞 K) K)ˣ →* ((v : S) → (v.1.adicCompletion K)ˣ) :=
  MonoidHom.pi fun v ↦ finUnitAt v.1

@[simp]
theorem finUnitsAt_apply (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : S) :
    finUnitsAt S b v = finUnitAt v.1 b :=
  rfl














variable {S}





end AtS

section Integrals

variable {S : Finset (HeightOneSpectrum (𝓞 K))}




end Integrals

end

end GroundTheory.Automorphic.GodementSection
