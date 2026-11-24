module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.PsiFEqOne
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

def SelfDualVol : Prop :=
  ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ L : AddSubgroup V, IsOpen (L : Set V) → IsCompact (L : Set V) →
    (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ y, Continuous fun x => χ x y) →
    (∀ y, (∀ x ∈ L, χ x y = 1) ↔ y ∈ L) → μ L = 1

def CosetInt : Prop :=
  ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (ν : Measure G) [ν.IsAddLeftInvariant]
    (H : AddSubgroup G), (∀ g : G, MeasurableSet {x : G | x - g ∈ H}) → ν H = 1 → Countable (G ⧸ H) →
    ∀ (f : G → ℂ) (fbar : G ⧸ H → ℂ), (∀ g, f g = fbar (QuotientAddGroup.mk g)) →
      (Integrable f ν ↔ Summable fun c => ‖fbar c‖) ∧ (Summable (fun c => ‖fbar c‖) → ∫ g, f g ∂ν = ∑' c, fbar c)

def TsumExhaust : Prop :=
  ∀ (α : Type) (f : α → ℂ) (C : ℕ → Finset α), Monotone C → (∀ a, ∃ k, a ∈ C k) →
    (∃ K : ℝ, ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) →
    Summable (fun a => ‖f a‖) ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a))

def NuPow : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (n k : ℕ),
    ∀ B ∈ hermMod σ ϖ n k, nuAt ϖ B = (q ^ 2) ^ Nat.log (q ^ 2) (nuAt ϖ B)

def NuBound : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (n k : ℕ) (r : ℝ), 0 ≤ r →
    (q : ℝ) ^ (n ^ 2) * r < 1 →
    ∑' B : hermMod σ ϖ n k, r ^ Nat.log (q ^ 2) (nuAt ϖ B.1) ≤ 1 / (1 - (q : ℝ) ^ (n ^ 2) * r)

def LevChars : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (c : Fv F v) (hc : c ∈ v.adicCompletionIntegers F), ‖c‖ = 1 → IsLevelChars σS hG.pS (hG.psiLev hc)

def VolLat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E), SdW F E σ M J (Fv F v) ψv n μv → μv (latV bs v) = 1

def HermitianLatticeVolumeOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ νv : Measure (HermR (Fv F v) σ n), SdHerm F E σ (Fv F v) ψv n νv → νv (H0 S σ n : Set (HermR (Fv F v) σ n)) = 1

def JtLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E), SdW F E σ M J (Fv F v) ψv n μv →
  ∀ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (hG.hermLev k X hX) =
      ((ε : ℂ) ^ M * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(M : ℤ))) ^
        Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS (red hG.pS k X))

def NuLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)), lam.IsAddHaarMeasure →
    (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v →
  ∀ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    nu2 lam L L (hG.hermLev k X hX).1 = (nuAt hG.pS (red hG.pS k X) : ℝ)

def PsiLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (hT : ∀ a b, σ (T b a) = T a b) (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 (hG.hermLev k X hX).1) =
      hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * red hG.pS k X))

def Exhaust : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ b : HermR (Fv F v) σ n, ∃ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X),
    b = hG.hermLev k X hX

def ClassLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (k : ℕ) (X X' : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X)
    (hX' : PositivityTheory.PfSWUS.Loc.cT σS X' = X'),
    hG.hermLev k X hX - hG.hermLev k X' hX' ∈ H0 S σ n ↔ red hG.pS k X = red hG.pS k X'

def HermitianLatticeInvariance : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  ∀ (hT : ∀ a b, σ (T b a) = T a b) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
    (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v → ∀ (z : ℂ) (b h : HermR (Fv F v) σ n), h ∈ H0 S σ n →
      whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z (b + h) =
        whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z b

def CosetMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : Fv F v → ℂ) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hG : GoodLoc σ J T bs v ψv S σS ϖ ε),
  MeasurableAdd (HermR (Fv F v) σ n) ∧ ∀ g : HermR (Fv F v) σ n, MeasurableSet {x | x - g ∈ H0 S σ n}

end PositivityTheory.SiegelWeilFormula.Gunr

end
