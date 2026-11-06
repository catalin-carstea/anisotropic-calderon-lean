import Calderon.NaturalAngularAdjoint

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.NaturalAngularAdjoint
open PrincipalCommutator ScalarBaseAdjoint ActualScalarPrincipalAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma hasCompactSupport_clm_apply (B : R3 → E →L[ℝ] E) (u : R3 → E)
    (hc : HasCompactSupport u) : HasCompactSupport (fun x => B x (u x)) := by
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp [hx]

lemma compact_weighted_inner_integrable (mu : R3 → ℝ) (u w : R3 → E)
    (hm : Continuous mu) (hu : Continuous u) (hw : Continuous w)
    (hc : HasCompactSupport u) :
    Integrable (fun x => mu x * ⟪u x, w x⟫_ℝ) := by
  have h := BaseDensityAdjoint.compact_inner_integrable (fun x => mu x • w x) u
    (hm.smul hw) hu hc
  simpa only [inner_smul_left, starRingEnd_apply, star_trivial, real_inner_comm] using h

lemma contDiff_scalarSecondBase (v : Fin 3 → R3) (a : MatrixField) (u : R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (scalarSecondBase v a u) := by
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (ha i j).smul (contDiff_directionalFDeriv (v i) _
      (contDiff_directionalFDeriv (v j) u hu))))

lemma hasCompactSupport_scalarSecondBase (v : Fin 3 → R3) (a : MatrixField)
    (u : R3 → E) (hc : HasCompactSupport u) :
    HasCompactSupport (scalarSecondBase v a u) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ =>
    HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ =>
      ((hc.fderiv_apply (𝕜 := ℝ) (v j)).fderiv_apply (𝕜 := ℝ) (v i)).smul_left
        (f := fun y => a y i j)))
  have he : (∑ i : Fin 3, ∑ j : Fin 3,
      (fun y => a y i j) • directionalFDeriv (v i) (directionalFDeriv (v j) u)) =
      scalarSecondBase v a u := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply', scalarSecondBase]
  rw [← he]
  exact h

lemma contDiff_scalarSecondBaseAdjoint (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (w : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hw : ContDiff ℝ ∞ w)
    (hp : ∀ x, mu x ≠ 0) : ContDiff ℝ ∞ (scalarSecondBaseAdjoint v mu a w) := by
  exact (hm.inv hp).smul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    contDiff_directionalFDeriv (v j) _ (contDiff_directionalFDeriv (v i) _
      ((hm.mul (ha i j)).smul hw)))))

lemma contDiff_angularFirstBase (v : Fin 3 → R3)
    (B : Fin 3 → R3 → E →L[ℝ] E) (u : R3 → E)
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (angularFirstBase v B u) := by
  exact ContDiff.sum (fun i _ => (hB i).clm_apply (contDiff_directionalFDeriv (v i) u hu))

lemma hasCompactSupport_angularFirstBase (v : Fin 3 → R3)
    (B : Fin 3 → R3 → E →L[ℝ] E) (u : R3 → E) (hc : HasCompactSupport u) :
    HasCompactSupport (angularFirstBase v B u) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ =>
    hasCompactSupport_clm_apply (B i) (directionalFDeriv (v i) u)
      (hc.fderiv_apply (𝕜 := ℝ) (v i)))
  have he : (∑ i : Fin 3, fun x => B i x (directionalFDeriv (v i) u x)) =
      angularFirstBase v B u := by
    funext x
    simp only [Finset.sum_apply, angularFirstBase]
  rw [← he]
  exact h

lemma contDiff_angularFirstBaseAdjoint (v : Fin 3 → R3) (mu : R3 → ℝ)
    (B : Fin 3 → R3 → E →L[ℝ] E) (w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hw : ContDiff ℝ ∞ w) (hp : ∀ x, mu x ≠ 0) :
    ContDiff ℝ ∞ (angularFirstBaseAdjoint v mu B w) := by
  exact ((hm.inv hp).neg).smul (ContDiff.sum (fun i _ =>
    contDiff_directionalFDeriv (v i) _
      (hm.smul ((contDiff_angularAdjoint (B i) (hB i)).clm_apply hw))))

/-- The full finite first-base sum has the proved density adjoint. -/
theorem compact_angularFirstBase_adjoint (v : Fin 3 → R3) (mu : R3 → ℝ)
    (B : Fin 3 → R3 → E →L[ℝ] E) (u w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport u) (hp : ∀ x, mu x ≠ 0) :
    (∫ x : R3, mu x * ⟪angularFirstBase v B u x, w x⟫_ℝ) =
      ∫ x : R3, mu x * ⟪u x, angularFirstBaseAdjoint v mu B w x⟫_ℝ := by
  have hiL (i : Fin 3) : Integrable (fun x : R3 =>
      mu x * ⟪B i x (directionalFDeriv (v i) u x), w x⟫_ℝ) := by
    exact compact_weighted_inner_integrable mu _ w hm.continuous
      ((hB i).clm_apply (contDiff_directionalFDeriv (v i) u hu)).continuous hw.continuous
      (hasCompactSupport_clm_apply (B i) _ (hc.fderiv_apply (𝕜 := ℝ) (v i)))
  have hiR (i : Fin 3) : Integrable (fun x : R3 =>
      mu x * ⟪u x, -(mu x)⁻¹ • directionalFDeriv (v i)
        (fun y => mu y • angularAdjoint (B i) y (w y)) x⟫_ℝ) := by
    exact compact_weighted_inner_integrable mu u _ hm.continuous hu.continuous
      ((((hm.inv hp).neg).smul (contDiff_directionalFDeriv (v i) _
        (hm.smul ((contDiff_angularAdjoint (B i) (hB i)).clm_apply hw)))).continuous) hc
  have hl : (fun x : R3 => mu x * ⟪angularFirstBase v B u x, w x⟫_ℝ) =
      fun x => ∑ i, mu x * ⟪B i x (directionalFDeriv (v i) u x), w x⟫_ℝ := by
    funext x
    simp only [angularFirstBase, sum_inner, Finset.mul_sum]
  have hr : (fun x : R3 => mu x * ⟪u x, angularFirstBaseAdjoint v mu B w x⟫_ℝ) =
      fun x => ∑ i, mu x * ⟪u x, -(mu x)⁻¹ • directionalFDeriv (v i)
        (fun y => mu y • angularAdjoint (B i) y (w y)) x⟫_ℝ := by
    funext x
    simp only [angularFirstBaseAdjoint, Finset.smul_sum, inner_sum, Finset.mul_sum]
  rw [hl, hr, integral_finsetSum _ (fun i _ => hiL i),
    integral_finsetSum _ (fun i _ => hiR i)]
  apply Finset.sum_congr rfl
  intro i _
  exact compact_angular_first_adjoint (v i) mu (B i) u w hm (hB i) hu hw hc hp

/-- Genuine full weighted formal-adjoint identity. This is a compact smooth-domain
 result, not equality of maximal closed unbounded operator domains. -/
theorem compact_naturalFormalAdjoint (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E) (u w : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport u) (hp : ∀ x, 0 < mu x) :
    (∫ x : R3, mu x * ⟪naturalOperator v a B C u x, w x⟫_ℝ) =
      ∫ x : R3, mu x * ⟪u x, naturalFormalAdjoint v mu a B C w x⟫_ℝ := by
  have hp0 : ∀ x, mu x ≠ 0 := fun x => ne_of_gt (hp x)
  have hsL := compact_weighted_inner_integrable mu (scalarSecondBase v a u) w
    hm.continuous (contDiff_scalarSecondBase v a u ha hu).continuous hw.continuous
    (hasCompactSupport_scalarSecondBase v a u hc)
  have hfL := compact_weighted_inner_integrable mu (angularFirstBase v B u) w
    hm.continuous (contDiff_angularFirstBase v B u hB hu).continuous hw.continuous
    (hasCompactSupport_angularFirstBase v B u hc)
  have hzL := compact_weighted_inner_integrable mu (fun x => C x (u x)) w
    hm.continuous (hC.clm_apply hu).continuous hw.continuous
    (hasCompactSupport_clm_apply C u hc)
  have hsR := compact_weighted_inner_integrable mu u (scalarSecondBaseAdjoint v mu a w)
    hm.continuous hu.continuous
    (contDiff_scalarSecondBaseAdjoint v mu a w hm ha hw hp0).continuous hc
  have hfR := compact_weighted_inner_integrable mu u (angularFirstBaseAdjoint v mu B w)
    hm.continuous hu.continuous
    (contDiff_angularFirstBaseAdjoint v mu B w hm hB hw hp0).continuous hc
  have hzR := compact_weighted_inner_integrable mu u (fun x => angularAdjoint C x (w x))
    hm.continuous hu.continuous ((contDiff_angularAdjoint C hC).clm_apply hw).continuous hc
  have hsLf : Integrable (fun x : R3 =>
      mu x * ⟪scalarSecondBase v a u x, w x⟫_ℝ +
      mu x * ⟪angularFirstBase v B u x, w x⟫_ℝ) := hsL.add hfL
  have hsRf : Integrable (fun x : R3 =>
      mu x * ⟪u x, scalarSecondBaseAdjoint v mu a w x⟫_ℝ +
      mu x * ⟪u x, angularFirstBaseAdjoint v mu B w x⟫_ℝ) := hsR.add hfR
  simp only [naturalOperator, naturalFormalAdjoint, inner_add_left, inner_add_right, mul_add]
  rw [integral_add hsLf hzL, integral_add hsL hfL,
    integral_add hsRf hzR, integral_add hsR hfR,
    compact_scalarSecondBase_adjoint v mu a u w hm ha hu hw hc hp,
    compact_angularFirstBase_adjoint v mu B u w hm hB hu hw hc hp0,
    compact_angular_zero_adjoint mu C u w]

lemma contDiff_adjointFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hp : ∀ x, mu x ≠ 0) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => adjointFirstCoefficient v mu a x i) := by
  exact (contDiff_const.mul (hm.inv hp)).mul (ContDiff.sum (fun j _ =>
    contDiff_directionalFDeriv (v j) _ (hm.mul (ha i j))))

lemma contDiff_adjointZeroCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hp : ∀ x, mu x ≠ 0) :
    ContDiff ℝ ∞ (adjointZeroCoefficient v mu a) := by
  exact (hm.inv hp).mul (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    contDiff_directionalFDeriv (v j) _
      (contDiff_directionalFDeriv (v i) _ (hm.mul (ha i j))))))

lemma contDiff_defectFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hp : ∀ x, mu x ≠ 0) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => defectFirstCoefficient v mu a B x i) := by
  exact (((contDiff_adjointFirstCoefficient v mu a hm ha hp i).smul contDiff_const).sub
    (hB i)).sub (contDiff_angularAdjoint (B i) (hB i))

lemma contDiff_defectZeroCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (B : Fin 3 → R3 → E →L[ℝ] E) (C : R3 → E →L[ℝ] E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hC : ContDiff ℝ ∞ C)
    (hp : ∀ x, mu x ≠ 0) : ContDiff ℝ ∞ (defectZeroCoefficient v mu a B C) := by
  exact ((((contDiff_adjointZeroCoefficient v mu a hm ha hp).smul contDiff_const).sub
    ((hm.inv hp).smul (ContDiff.sum (fun i _ =>
      contDiff_directionalFDeriv (v i) _ (hm.smul (contDiff_angularAdjoint (B i) (hB i))))))).add
    (contDiff_angularAdjoint C hC)).sub hC

/-- The actual computed defect first coefficient has no third-base term against
 the scalar principal part. Smoothness of the computed coefficient is derived. -/
theorem defect_first_scalar_principal_commutator (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (B : Fin 3 → R3 → E →L[ℝ] E)
    (w : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hB : ∀ i, ContDiff ℝ ∞ (B i)) (hw : ContDiff ℝ ∞ w)
    (hp : ∀ x, mu x ≠ 0) (i j k : Fin 3) (x : R3) :
    defectFirstCoefficient v mu a B x k
      (directionalFDeriv (v k) (fun y => a y i j •
        directionalFDeriv (v i) (directionalFDeriv (v j) w) y) x) -
      a x i j • directionalFDeriv (v i) (directionalFDeriv (v j)
        (fun y => defectFirstCoefficient v mu a B y k
          (directionalFDeriv (v k) w y))) x =
    directionalFDeriv (v k) (fun y => a y i j) x •
      defectFirstCoefficient v mu a B x k
        (directionalFDeriv (v i) (directionalFDeriv (v j) w) x) -
    a x i j • directionalFDeriv (v i)
      (directionalFDeriv (v j) (fun y => defectFirstCoefficient v mu a B y k)) x
        (directionalFDeriv (v k) w x) -
    a x i j • directionalFDeriv (v j)
      (fun y => defectFirstCoefficient v mu a B y k) x
        (directionalFDeriv (v i) (directionalFDeriv (v k) w) x) -
    a x i j • directionalFDeriv (v i)
      (fun y => defectFirstCoefficient v mu a B y k) x
        (directionalFDeriv (v j) (directionalFDeriv (v k) w) x) := by
  exact scalar_principal_directional_commutator (v i) (v j) (v k)
    (fun y => a y i j) (fun y => defectFirstCoefficient v mu a B y k) w
    (ha i j) (contDiff_defectFirstCoefficient v mu a B hm ha hB hp k) hw x

end OAI.AnisotropicCalderon.NaturalAngularAdjoint
