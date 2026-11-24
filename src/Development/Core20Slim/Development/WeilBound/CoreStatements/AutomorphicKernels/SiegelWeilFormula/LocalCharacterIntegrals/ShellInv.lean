module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellP
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.TracePairSums.ShellConj
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem jtR_conj_inv (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : Fv F v → ℂ) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    [μv.IsAddHaarMeasure] (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (hΦ : IsSB Φv) :
    ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → ∀ b b' : HermR (Fv F v) σ n,
      (b' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = ((1 + x).map (sigR (Fv F v) σ))ᵀ * b * (1 + x) →
      jtR (Fv F v) σ J ψR μv Φv b' = jtR (Fv F v) σ J ψR μv Φv b :=
  SwSplit.jtR_conj_inv' v σ hcm J ψR μv Φv hΦ

end PositivityTheory.SiegelWeilFormula.SwLocFin
