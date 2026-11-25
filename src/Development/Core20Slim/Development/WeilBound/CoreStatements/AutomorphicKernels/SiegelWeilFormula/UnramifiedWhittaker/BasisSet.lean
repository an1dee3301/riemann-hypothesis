module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def basisSet (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) : Finset F :=
  (Finset.univ.image fun p : Fin d × Fin d × Fin d => bs.repr (bs p.1 * bs p.2.1) p.2.2) ∪
  (Finset.univ.image fun k : Fin d => bs.repr 1 k) ∪
  (Finset.univ.image fun p : Fin d × Fin d => bs.repr (σ (bs p.1)) p.2) ∪
  {Algebra.discr F (⇑bs), (Algebra.discr F (⇑bs))⁻¹, (2 : F)⁻¹}


open Classical in
def matSet {d : ℕ} (bs : Module.Basis (Fin d) F E) {m : ℕ} (X : Matrix (Fin m) (Fin m) E) : Finset F :=
  (Finset.univ.image fun p : Fin m × Fin m × Fin d => bs.repr (X p.1 p.2.1) p.2.2) ∪
  (Finset.univ.image fun k : Fin d => bs.repr (X.det)⁻¹ k)

def IntAt (v : HeightOneSpectrum (𝓞 F)) (X : Finset F) : Prop :=
  ∀ x ∈ X, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F

def FinInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Finset F), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IntAt v X

def PsiBasic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    (∀ x y, psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y) ∧ psiV F ψ v 0 = 1 ∧ Continuous (psiV F ψ v)

def PsiCond : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ a : Fv F v,
      (∀ b ∈ v.adicCompletionIntegers F, psiV F ψ v (a * b) = 1) ↔ a ∈ v.adicCompletionIntegers F

def LocRing : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)), IntAt v (basisSet σ bs) →
  ∃ (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S),
    (ε = 1 ∨ ε = -1) ∧ (S : Set (Fv F v ⊗[F] E)) = Rv bs v ∧
    (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) ∧
    (∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c) ∧
    ϖ ∈ v.adicCompletionIntegers F ∧ ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧
    IsUnrQuad S σS ⟨_, hϖ⟩ (Ideal.absNorm v.asIdeal) ε ∧ ‖(2 : Fv F v)‖ = 1 ∧
    ∀ a : Fv F v ⊗[F] E,
      (∀ b ∈ S, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * b) ∈ v.adicCompletionIntegers F) ↔ a ∈ S

def LocMat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S),
    (S : Set (Fv F v ⊗[F] E)) = Rv bs v → (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) →
  ∀ (m : ℕ) (X : Matrix (Fin m) (Fin m) E), (∀ a b, σ (X b a) = X a b) → X.det ≠ 0 → IntAt v (matSet bs X) →
    ∃ hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S, IsUnimod σS (matS S X hX)

end PositivityTheory.SiegelWeilFormula.Gunr

end
