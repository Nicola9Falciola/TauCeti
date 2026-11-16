/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic

/-!
# Upper-triangular defining ideals after conjugation

If conjugation by a constant invertible matrix makes an algebra-valued point upper triangular,
then that point kills the upper-triangular defining ideal pulled back along the inverse coordinate
automorphism. The criterion applies over any commutative base ring; it is the upper-triangular
case of `TauCeti.GeneralLinear.comapOfSurjective_conjCoordinateIso_inv_toIdeal_le_ker_iff`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.UpperTriangular

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A point whose matrix becomes upper triangular after conjugation by `P` kills the defining
ideal pulled back along the inverse coordinate automorphism. -/
theorem comap_le_ker_of_conjugate
    (P : Matrix.GeneralLinearGroup (Fin n) R) {A : Type v} [CommRing A] [Algebra R A]
    (f : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] A)
    (hf : ((Matrix.GeneralLinearGroup.map (algebraMap R A) P *
        GeneralLinear.pointsMulEquiv n (toConv f) *
        (Matrix.GeneralLinearGroup.map (algebraMap R A) P)⁻¹ :
          Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A).IsUpperTriangular) :
    ((GeneralLinear.UpperTriangular.definingHopfIdeal R n).comapOfSurjective
      (GeneralLinear.conjCoordinateIso P).inv.hom
      (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso P).inv).2).toIdeal ≤
        RingHom.ker f.toRingHom :=
  (GeneralLinear.comapOfSurjective_conjCoordinateIso_inv_toIdeal_le_ker_iff _ P
    (toConv f)).mpr <| by rwa [hopfIdealPointsSubgroup_eq, UpperTriangularGroup.mem_iff]

end TauCeti.GeneralLinear.UpperTriangular
