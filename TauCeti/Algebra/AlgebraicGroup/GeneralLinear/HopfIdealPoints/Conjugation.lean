/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic

/-!
# Hopf-ideal point subgroups of `GLₙ` after conjugation

A Hopf ideal `J` of the coordinate Hopf algebra of `GLₙ` over `R` cuts out a subgroup of
`GLₙ(A)` for every `R`-algebra `A`. This file reads membership of a conjugated point in that
subgroup on coordinates: if conjugation by a constant invertible matrix `P` carries the matrix of
a point `f` into the subgroup cut out by `J`, then `f` kills the preimage of `J` under the inverse
of the coordinate automorphism of conjugation by `P`.

## Main results

* `TauCeti.GeneralLinear.comapOfSurjective_conjCoordinateIso_inv_toIdeal_le_ker`: the criterion
  above, over any commutative base ring and any value algebra.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- **A point conjugated into a Hopf-ideal point subgroup kills the pulled-back ideal.** If
conjugation by `P` carries the matrix of a point `f` of `GLₙ` over `A` into the subgroup cut out
by `J`, then `f` kills the image of `J` under the coordinate automorphism of conjugation by `P`,
that is, the preimage of `J` under the inverse automorphism. -/
theorem comapOfSurjective_conjCoordinateIso_inv_toIdeal_le_ker
    (J : HopfIdeal R (coordinateHopfAlgebra R n)) (P : Matrix.GeneralLinearGroup (Fin n) R)
    {A : Type v} [CommRing A] [Algebra R A] (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A))
    (hf : Matrix.GeneralLinearGroup.map (algebraMap R A) P * pointsMulEquiv n f *
        (Matrix.GeneralLinearGroup.map (algebraMap R A) P)⁻¹ ∈ hopfIdealPointsSubgroup n J A) :
    (J.comapOfSurjective (conjCoordinateIso P).inv.hom
        (ConcreteCategory.bijective_of_isIso (conjCoordinateIso P).inv).2).toIdeal ≤
      RingHom.ker f.ofConv.toRingHom := by
  rw [← pointsMulEquiv_toConv_comp_conjCoordinateIso, mem_hopfIdealPointsSubgroup_iff,
    MulEquiv.symm_apply_apply] at hf
  intro y hy
  have hzero := hf _ (HopfIdeal.mem_comapOfSurjective.mp hy)
  rw [ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom, ← _root_.CommHopfAlgCat.comp_apply,
    Iso.inv_hom_id, _root_.CommHopfAlgCat.id_apply] at hzero
  rwa [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

end TauCeti.GeneralLinear
