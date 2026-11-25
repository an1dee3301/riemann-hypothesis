module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderStableIntegralStructure
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_stable_integral_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) = (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | exact GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | (intros; apply GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat <;> assumption)
