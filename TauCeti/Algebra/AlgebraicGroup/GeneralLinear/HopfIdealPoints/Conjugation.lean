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
`GLₙ(A)` for every `R`-algebra `A`. Conjugation by a constant invertible matrix `P` acts on the
coordinate Hopf algebra by an automorphism, and this file identifies the subgroup cut out by the
preimage of `J` under the inverse of that automorphism: a matrix `g` lies in it exactly when
`P g P⁻¹` lies in the subgroup cut out by `J`. Read on coordinates, a point `f` kills that
preimage exactly when conjugation by `P` carries its matrix into the subgroup cut out by `J`.

## Main results

* `TauCeti.GeneralLinear.mem_hopfIdealPointsSubgroup_comapOfSurjective_conjCoordinateIso_inv_iff`:
  the matrix criterion above, over any commutative base ring and any value algebra.
* `TauCeti.GeneralLinear.comapOfSurjective_conjCoordinateIso_inv_toIdeal_le_ker_iff`: the same
  criterion as a kernel containment for an algebra-valued point.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- **Membership in a Hopf-ideal point subgroup after conjugation.** A matrix `g` lies in the
subgroup cut out by the image of `J` under the coordinate automorphism of conjugation by `P`, that
is, by the preimage of `J` under the inverse automorphism, exactly when `P g P⁻¹` lies in the
subgroup cut out by `J`. -/
theorem mem_hopfIdealPointsSubgroup_comapOfSurjective_conjCoordinateIso_inv_iff
    (J : HopfIdeal R (coordinateHopfAlgebra R n)) (P : Matrix.GeneralLinearGroup (Fin n) R)
    {A : Type v} [CommRing A] [Algebra R A] (g : Matrix.GeneralLinearGroup (Fin n) A) :
    g ∈ hopfIdealPointsSubgroup n (J.comapOfSurjective (conjCoordinateIso P).inv.hom
        (ConcreteCategory.bijective_of_isIso (conjCoordinateIso P).inv).2) A ↔
      Matrix.GeneralLinearGroup.map (algebraMap R A) P * g *
          (Matrix.GeneralLinearGroup.map (algebraMap R A) P)⁻¹ ∈
        hopfIdealPointsSubgroup n J A := by
  obtain ⟨f, rfl⟩ := (pointsMulEquiv (R := R) (A := A) n).surjective g
  rw [← pointsMulEquiv_toConv_comp_conjCoordinateIso, mem_hopfIdealPointsSubgroup_iff,
    mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  simp only [HopfIdeal.mem_comapOfSurjective, AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  refine ⟨fun hf y hy => hf _ ?_, fun hf x hx => ?_⟩
  · rwa [← _root_.CommHopfAlgCat.comp_apply, Iso.hom_inv_id, _root_.CommHopfAlgCat.id_apply]
  · simpa only [← _root_.CommHopfAlgCat.comp_apply, Iso.inv_hom_id,
      _root_.CommHopfAlgCat.id_apply] using hf _ hx

/-- **A point kills the pulled-back ideal exactly when conjugation carries it into the
Hopf-ideal point subgroup.** A point `f` of `GLₙ` over `A` kills the image of `J` under the
coordinate automorphism of conjugation by `P`, that is, the preimage of `J` under the inverse
automorphism, exactly when conjugation by `P` carries the matrix of `f` into the subgroup cut out
by `J`. -/
theorem comapOfSurjective_conjCoordinateIso_inv_toIdeal_le_ker_iff
    (J : HopfIdeal R (coordinateHopfAlgebra R n)) (P : Matrix.GeneralLinearGroup (Fin n) R)
    {A : Type v} [CommRing A] [Algebra R A] (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (J.comapOfSurjective (conjCoordinateIso P).inv.hom
        (ConcreteCategory.bijective_of_isIso (conjCoordinateIso P).inv).2).toIdeal ≤
      RingHom.ker f.ofConv.toRingHom ↔
    Matrix.GeneralLinearGroup.map (algebraMap R A) P * pointsMulEquiv n f *
        (Matrix.GeneralLinearGroup.map (algebraMap R A) P)⁻¹ ∈ hopfIdealPointsSubgroup n J A := by
  rw [← mem_hopfIdealPointsSubgroup_comapOfSurjective_conjCoordinateIso_inv_iff,
    ← pointToGeneralLinear_mem_hopfIdealPointsSubgroup_iff_toIdeal_le_ker, toConv_ofConv,
    pointsMulEquiv_apply]

end TauCeti.GeneralLinear
