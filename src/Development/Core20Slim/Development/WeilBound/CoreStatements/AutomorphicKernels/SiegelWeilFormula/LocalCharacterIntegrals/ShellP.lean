module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (E) in
def bA (v : HeightOneSpectrum (𝓞 F)) : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)

def crd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v ⊗[F] E) : Fin (Module.finrank F E) → Fv F v :=
  (bA E v).equivFun a

def nA (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v ⊗[F] E) : ℝ := ‖crd v a‖

def nV (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : Fin n → Fv F v ⊗[F] E) : ℝ := ‖fun i => crd v (y i)‖

def nM (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (x : Fin p → Fin q → Fv F v ⊗[F] E) : ℝ :=
  ‖fun i j => crd v (x i j)‖

structure Hyp (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (g : HermR (Fv F v) σ n → ℂ) (T : HermR (Fv F v) σ n) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  chr : IsCharAF F ψ
  sdW : SdW F E σ M J (Fv F v) (psiV F ψ v) n μv
  sdH : SdHerm F E σ (Fv F v) (psiV F ψ v) n νv
  haar : lam.IsAddHaarMeasure
  co₁ : IsCO L₁
  co₂ : IsCO L₂
  sb : IsSB Φv
  dens : IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv g
  unit : IsUnit (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det

def uu (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (T : HermR (Fv F v) σ n) (b : HermR (Fv F v) σ n) : ℂ :=
  jtR (Fv F v) σ J (psiV F ψ v) μv Φv b * psiV F ψ v (-trPair (Fv F v) T.1 b.1)

def ShellP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) μv νv lam L₁ L₂ Φv g T,
    Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T → ∀ q : ℝ, 1 < q → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ z : ℂ,
      ∫ b in {b : HermR (Fv F v) σ n | R < nM v b.1 ∧ nM v b.1 ≤ q * R},
        whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b ∂νv = 0

def ConvP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) μv νv lam L₁ L₂ Φv g T,
    Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z) νv

def DualP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) μv νv lam L₁ L₂ Φv g T,
    Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T →
      Tendsto (fun R : ℝ => ∫ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R}, uu σ J ψ v μv Φv T b ∂νv) atTop (𝓝 (g T))

end PositivityTheory.SiegelWeilFormula.SwLocFin
