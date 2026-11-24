module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.ArchDecay

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infAd (a : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)

def arch (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def dD (v : κ → mixedEmbedding.mixedSpace F) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  deriv (fun t : ℝ => f (x + fun i => infAd F (t • v i))) 0

def mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  (l (arch F x) : ℂ) * f x


variable (κ) in
abbrev Op : Type := (κ → mixedEmbedding.mixedSpace F) ⊕ ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)

def app (o : Op F κ) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := Sum.elim (fun v => dD F v f) (fun l => mM F l f) o

def size (o : Op F κ) : ℝ := Sum.elim (fun v => ‖v‖) (fun l => ‖l‖) o

def word (w : List (Op F κ)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := w.foldr (fun o g => app F o g) f

def wordD (w : List (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  word F (w.map Sum.inl) f

def Per (m : ℕ) (f : (κ → AF F) → ℂ) : Prop :=
  ∀ x z : κ → AF F, (∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    z i = (m : AF F) * a) → f (x + z) = f x

@[simp] theorem word_cons (o : Op F κ) (w : List (Op F κ)) (f : (κ → AF F) → ℂ) :
    word F (o :: w) f = app F o (word F w f) := rfl

theorem word_append (w w' : List (Op F κ)) (f : (κ → AF F) → ℂ) : word F (w ++ w') f = word F w (word F w' f) := by
  simp [word, List.foldr_append]

end GlobalTheory.ArchDecay
