module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScale
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ → GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  first | exact @GlobalTheory.VacRead.rl_div_scale | exact GlobalTheory.VacRead.rl_div_scale | (intros; apply GlobalTheory.VacRead.rl_div_scale <;> assumption)
