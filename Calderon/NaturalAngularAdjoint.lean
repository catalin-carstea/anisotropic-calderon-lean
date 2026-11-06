import Calderon.ActualPerturbedDefect
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.NaturalAngularAdjoint
open PrincipalCommutator ScalarBaseAdjoint ActualScalarPrincipalAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The pointwise angular adjoint is the genuine Hilbert adjoint. -/
def angularAdjoint (B : R3 → E →L[ℝ] E) : R3 → E →L[ℝ] E :=
  fun x => ContinuousLinearMap.adjoint (B x)

lemma contDiff_angularAdjoint (B : R3 → E →L[ℝ] E) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (angularAdjoint B) := by
  exact (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).contDiff.comp hB

lemma angularAdjoint_inner (B : R3 → E →L[ℝ] E) (x : R3) (u w : E) :
    ⟪B x u, w⟫_ℝ = ⟪u, angularAdjoint B x w⟫_ℝ := by
  exact (ContinuousLinearMap.adjoint_inner_right (B x) u w).symm

/-- Integration by parts for the actual first-base angular term, with the whole
 density and angular adjoint kept inside the derivative. -/
theorem compact_angular_first_adjoint (v : R3) (mu : R3 → ℝ)
    (B : R3 → E →L[ℝ] E) (u w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hB : ContDiff ℝ ∞ B)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport u) (hp : ∀ x, mu x ≠ 0) :
    (∫ x : R3, mu x * ⟪B x (directionalFDeriv v u x), w x⟫_ℝ) =
      ∫ x : R3, mu x * ⟪u x, -(mu x)⁻¹ •
        directionalFDeriv v (fun y => mu y • angularAdjoint B y (w y)) x⟫_ℝ := by
  have hb := contDiff_angularAdjoint B hB
  have h := BaseDensityAdjoint.compact_inner_directionalDeriv v
    (fun y => mu y • angularAdjoint B y (w y)) u
    (hm.smul (hb.clm_apply hw)) hu hc
  have hl : (fun x : R3 => mu x * ⟪B x (directionalFDeriv v u x), w x⟫_ℝ) =
      fun x => ⟪mu x • angularAdjoint B x (w x), directionalFDeriv v u x⟫_ℝ := by
    funext x
    rw [inner_smul_left, angularAdjoint_inner, real_inner_comm]
    rfl
  have hr : (fun x : R3 => mu x * ⟪u x, -(mu x)⁻¹ •
      directionalFDeriv v (fun y => mu y • angularAdjoint B y (w y)) x⟫_ℝ) =
      fun x => -⟪directionalFDeriv v
        (fun y => mu y • angularAdjoint B y (w y)) x, u x⟫_ℝ := by
    funext x
    have hmu : mu x * -(mu x)⁻¹ = -1 := by
      rw [mul_neg, mul_inv_cancel₀ (hp x)]
    rw [inner_smul_right, ← mul_assoc, hmu, neg_one_mul, real_inner_comm]
  rw [hl, hr, integral_neg]
  exact h

/-- A smooth zero-base angular coefficient has exactly its pointwise angular adjoint. -/
theorem compact_angular_zero_adjoint (mu : R3 → ℝ) (C : R3 → E →L[ℝ] E)
    (u w : R3 → E) :
    (∫ x : R3, mu x * ⟪C x (u x), w x⟫_ℝ) =
      ∫ x : R3, mu x * ⟪u x, angularAdjoint C x (w x)⟫_ℝ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z : ℝ => mu x * z) (angularAdjoint_inner C x (u x) (w x)))

/-- The first-base part of the source-coordinate perturbation. -/
def angularFirstBase (v : Fin 3 → R3) (B : Fin 3 → R3 → E →L[ℝ] E)
    (u : R3 → E) (x : R3) : E :=
  ∑ i, B i x (directionalFDeriv (v i) u x)

/-- Full base-density adjoint of the first-base part. -/
def angularFirstBaseAdjoint (v : Fin 3 → R3) (mu : R3 → ℝ)
    (B : Fin 3 → R3 → E →L[ℝ] E) (w : R3 → E) (x : R3) : E :=
  -(mu x)⁻¹ • ∑ i, directionalFDeriv (v i)
    (fun y => mu y • angularAdjoint (B i) y (w y)) x

/-- Genuine coordinate U with real scalar second principal and angular lower coefficients. -/
def naturalOperator (v : Fin 3 → R3) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E)
    (u : R3 → E) (x : R3) : E :=
  scalarSecondBase v a u x + angularFirstBase v B u x + C x (u x)

/-- The candidate is proved to be the formal adjoint on the smooth compact domain below. -/
def naturalFormalAdjoint (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E)
    (w : R3 → E) (x : R3) : E :=
  scalarSecondBaseAdjoint v mu a w x + angularFirstBaseAdjoint v mu B w x +
    angularAdjoint C x (w x)

/-- Derivative of the actual weighted angular adjoint coefficient. -/
def weightedAngularAdjointDerivative (v : R3) (mu : R3 → ℝ)
    (B : R3 → E →L[ℝ] E) : R3 → E →L[ℝ] E :=
  directionalFDeriv v (fun y => mu y • angularAdjoint B y)

lemma weightedAngularAdjointDerivative_apply (v : R3) (mu : R3 → ℝ)
    (B : R3 → E →L[ℝ] E) (hm : ContDiff ℝ ∞ mu) (hB : ContDiff ℝ ∞ B)
    (x : R3) (z : E) :
    weightedAngularAdjointDerivative v mu B x z =
      directionalFDeriv v mu x • angularAdjoint B x z +
        mu x • directionalFDeriv v (angularAdjoint B) x z := by
  rw [weightedAngularAdjointDerivative,
    directionalFDeriv_smul v mu (angularAdjoint B) hm (contDiff_angularAdjoint B hB)]
  rfl

lemma angular_first_adjoint_term (v : R3) (mu : R3 → ℝ)
    (B : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hB : ContDiff ℝ ∞ B)
    (hw : ContDiff ℝ ∞ w) (x : R3) (hp : mu x ≠ 0) :
    -(mu x)⁻¹ • directionalFDeriv v
      (fun y => mu y • angularAdjoint B y (w y)) x =
      -angularAdjoint B x (directionalFDeriv v w x) -
        (mu x)⁻¹ • weightedAngularAdjointDerivative v mu B x (w x) := by
  have hb : ContDiff ℝ ∞ (fun y => mu y • angularAdjoint B y) :=
    hm.smul (contDiff_angularAdjoint B hB)
  have he : (fun y => mu y • angularAdjoint B y (w y)) =
      fun y => (mu y • angularAdjoint B y) (w y) := rfl
  have hd := directionalFDeriv_clm_apply v (fun y => mu y • angularAdjoint B y) w hb hw x
  rw [he, hd]
  simp only [weightedAngularAdjointDerivative, ContinuousLinearMap.smul_apply,
    smul_add, smul_smul]
  have hc : -(mu x)⁻¹ * mu x = -1 := by
    rw [neg_mul, inv_mul_cancel₀ hp]
  rw [hc]
  module

lemma angularFirstBaseAdjoint_coefficient_form (v : Fin 3 → R3) (mu : R3 → ℝ)
    (B : Fin 3 → R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hw : ContDiff ℝ ∞ w) (x : R3) (hp : mu x ≠ 0) :
    angularFirstBaseAdjoint v mu B w x =
      ∑ i, (-angularAdjoint (B i) x (directionalFDeriv (v i) w x) -
        (mu x)⁻¹ • weightedAngularAdjointDerivative (v i) mu (B i) x (w x)) := by
  unfold angularFirstBaseAdjoint
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact angular_first_adjoint_term (v i) mu (B i) w hm (hB i) hw x hp

/-- Exact first-base coefficient of U†−U, including B and the actual sphere adjoint B*. -/
def defectFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (x : R3) (i : Fin 3) : E →L[ℝ] E :=
  adjointFirstCoefficient v mu a x i • ContinuousLinearMap.id ℝ E -
    B i x - angularAdjoint (B i) x

/-- Exact zero-base coefficient: all density and angular adjoint derivatives retained. -/
def defectZeroCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (x : R3) : E →L[ℝ] E :=
  adjointZeroCoefficient v mu a x • ContinuousLinearMap.id ℝ E -
    (mu x)⁻¹ • ∑ i, weightedAngularAdjointDerivative (v i) mu (B i) x +
    angularAdjoint C x - C x

/-- Full source-coordinate defect, proved from scalar product differentiation and
 genuine angular adjoints. There is no second-base derivative on the right. -/
theorem naturalFormalAdjoint_sub (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hw : ContDiff ℝ ∞ w)
    (x : R3) (hp : mu x ≠ 0) (hs : ∀ᶠ y in 𝓝 x, (a y).IsHermitian) :
    naturalFormalAdjoint v mu a B C w x - naturalOperator v a B C w x =
      defectZeroCoefficient v mu a B C x (w x) +
      ∑ i, defectFirstCoefficient v mu a B x i (directionalFDeriv (v i) w x) := by
  have hscalar := scalarSecondBaseAdjoint_coefficient_form v mu a w hm ha hw x hp hs
  have hfirst := angularFirstBaseAdjoint_coefficient_form v mu B w hm hB hw x hp
  have he : naturalFormalAdjoint v mu a B C w x - naturalOperator v a B C w x =
      (scalarSecondBaseAdjoint v mu a w x - scalarSecondBase v a w x) +
      (angularFirstBaseAdjoint v mu B w x - angularFirstBase v B w x) +
      (angularAdjoint C x (w x) - C x (w x)) := by
    unfold naturalFormalAdjoint naturalOperator
    abel
  rw [he, hscalar, hfirst]
  simp only [angularFirstBase, defectFirstCoefficient, defectZeroCoefficient,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sum_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.smul_sum, Finset.sum_neg_distrib]
  module

/-- The complete angular-coefficient defect with the actual reference density,
 actual shrinking radius and real symmetric perturbed principal matrix.
 B,C are explicit bounded Hilbert coefficient families. -/
theorem actual_naturalFormalAdjoint_sub (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (w : R3 → E)
    (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hw : ContDiff ℝ ∞ w)
    (x : R3) (hs : ∀ᶠ y in 𝓝 x, (h y).IsHermitian) :
    naturalFormalAdjoint ReferenceDensityBounds.coordinateDirection
      (fun y => ReferenceDensityBounds.referenceDensityFamily g L (lam,y))
      (actualPrincipalMatrix g L lam δ R p h) B C w x -
      naturalOperator ReferenceDensityBounds.coordinateDirection
        (actualPrincipalMatrix g L lam δ R p h) B C w x =
    defectZeroCoefficient ReferenceDensityBounds.coordinateDirection
      (fun y => ReferenceDensityBounds.referenceDensityFamily g L (lam,y))
      (actualPrincipalMatrix g L lam δ R p h) B C x (w x) +
    ∑ i, defectFirstCoefficient ReferenceDensityBounds.coordinateDirection
      (fun y => ReferenceDensityBounds.referenceDensityFamily g L (lam,y))
      (actualPrincipalMatrix g L lam δ R p h) B x i
      (directionalFDeriv (ReferenceDensityBounds.coordinateDirection i) w x) := by
  apply naturalFormalAdjoint_sub
  · exact (ReferenceDensityBounds.contDiff_referenceDensityFamily g hg L).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun y : R3 => (lam,y)))
  · exact ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry
      g hg L lam δ R p h hδ hR hh
  · exact hB
  · exact hw
  · exact ne_of_gt (ReferenceDensityBounds.referenceDensityFamily_pos g hg L (lam,x))
  · filter_upwards [hs] with y hy
    exact ActualPerturbedDefect.actualPrincipalMatrix_isHermitian g hg L lam δ R p h y hy

end OAI.AnisotropicCalderon.NaturalAngularAdjoint
