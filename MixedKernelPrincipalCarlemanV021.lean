import MixedKernelPhaseRoomsV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

/-! N1–N2 (REPORT.md v019 §N, written before this code): native Carleman for the LITERAL
principal coefficient `vol g • g⁻¹` of an admissible metric, through the SAME producers. -/
namespace OAI.AnisotropicCalderon.StrictWeightCarleman
open scoped ContDiff
open OAI.AnisotropicCalderon.EnergyBridge (principalCoefficient)

/-- N1: the inverse differentiation rule for an admissible metric, PROVED. -/
theorem pd_metric_inverse_entry (g : MatrixField) (hg : IsAdmissibleMetric g) (x : R3)
    (r i j : Fin 3) :
    pd r (fun y => (g y)⁻¹ i j) x =
      -∑ s, ∑ t, (g x)⁻¹ i s * pd r (fun y => g y s t) x * (g x)⁻¹ t j := by
  have hA := OAI.AnisotropicCalderon.EnergyBridge.contDiff_metric_inverse_entry g hg
  have hU : ∀ y, IsUnit (g y).det := fun y =>
    (Matrix.isUnit_iff_isUnit_det _).mp (hg.posDef y).isUnit
  have hid : ∀ s j, (fun y => ∑ t, g y s t * (g y)⁻¹ t j) =
      fun _ => (if s = j then 1 else 0 : ℝ) := by
    intro s j
    funext y
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv (g y) (hU y)) s) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have h0 : ∀ s j, ∑ t, (pd r (fun y => g y s t) x * (g x)⁻¹ t j +
      g x s t * pd r (fun y => (g y)⁻¹ t j) x) = 0 := by
    intro s j
    have e : pd r (fun y => ∑ t, g y s t * (g y)⁻¹ t j) x =
        pd r (fun _ => (if s = j then 1 else 0 : ℝ)) x := by
      rw [hid s j]
    rw [pd_sum (fun t => (hg.smooth s t).mul (hA t j)), pd_const] at e
    rw [← e]
    exact Finset.sum_congr rfl fun t _ => (pd_mul (hg.smooth s t) (hA t j) x).symm
  have hL : ∀ i t, ∑ s, (g x)⁻¹ i s * g x s t = if i = t then 1 else 0 := by
    intro i t
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul (g x) (hU x)) i) t
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have key : pd r (fun y => (g y)⁻¹ i j) x =
      ∑ t, (if i = t then 1 else 0 : ℝ) * pd r (fun y => (g y)⁻¹ t j) x := by
    simp
  rw [key]
  have e0 := h0 0 j
  have e1 := h0 1 j
  have e2 := h0 2 j
  have l0 := hL i 0
  have l1 := hL i 1
  have l2 := hL i 2
  simp only [Fin.sum_univ_three] at e0 e1 e2 l0 l1 l2 ⊢
  linear_combination (g x)⁻¹ i 0 * e0 + (g x)⁻¹ i 1 * e1 + (g x)⁻¹ i 2 * e2 -
    pd r (fun y => (g y)⁻¹ 0 j) x * l0 - pd r (fun y => (g y)⁻¹ 1 j) x * l1 -
    pd r (fun y => (g y)⁻¹ 2 j) x * l2

/-- N2: native Carleman for the literal principal coefficient `vol g • g⁻¹`, from the
source metric strictness of the SAME phase `θ`, via `point_criterion_of_metric_strictness`,
`point_strictness_smul` (`ρ = vol g`) and `local_strict_weight_carleman_of_point_strictness`. -/
theorem principal_carleman_of_metric_strictness (g : MatrixField) (hg : IsAdmissibleMetric g)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (hdθ : (fun k => pd k θ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, g p i j * v i * v j = 1 →
      ∑ i, ∑ j, g p i j * phaseField (fun i k y => (g y)⁻¹ i k) θ i p * v j = 0 →
      0 < (∑ i, ∑ j, christoffelHess (fun i j y => g y i j) (fun i k y => (g y)⁻¹ i k) θ p i j *
          phaseField (fun i k y => (g y)⁻¹ i k) θ i p *
          phaseField (fun i k y => (g y)⁻¹ i k) θ j p) /
          phaseNorm (fun i k y => (g y)⁻¹ i k) θ p +
        ∑ i, ∑ j, christoffelHess (fun i j y => g y i j) (fun i k y => (g y)⁻¹ i k) θ p i j *
          v i * v j) :
    ∃ m r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * θ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * θ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * θ x)) *
          Lop (fun i k y => principalCoefficient g y i k) w x ^ 2 := by
  have hA : ∀ i k, ContDiff ℝ ∞ (fun y => (g y)⁻¹ i k) :=
    OAI.AnisotropicCalderon.EnergyBridge.contDiff_metric_inverse_entry g hg
  have hsymm : ∀ i k, (fun y => (g y)⁻¹ i k) = fun y => (g y)⁻¹ k i := by
    intro i k
    funext y
    simpa only [star_trivial] using ((hg.posDef y).inv.isHermitian.apply k i)
  have hU : IsUnit (g p).det := (Matrix.isUnit_iff_isUnit_det _).mp (hg.posDef p).isUnit
  have hGA : ∀ i k, ∑ j, g p i j * (g p)⁻¹ j k = if i = k then 1 else 0 := by
    intro i k
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv (g p) hU) i) k
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have hGpos : ∀ v : Fin 3 → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, g p i j * v i * v j := by
    intro v hv
    have h := (hg.posDef p).dotProduct_mulVec_pos hv
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at h ⊢
    linarith
  obtain ⟨hN, hcrit⟩ := point_criterion_of_metric_strictness (G := fun i j y => g y i j)
    hA hθ hsymm p (fun r i j => pd_metric_inverse_entry g hg p r i j) hGA hGpos hdθ hsrc
  have hvol : 0 < OAI.AnisotropicCalderon.vol g p :=
    Real.sqrt_pos.mpr (hg.posDef p).det_pos
  obtain ⟨hNb, hcritb⟩ := point_strictness_smul (b := fun i k y => principalCoefficient g y i k)
    (fun i k z => by simp [principalCoefficient])
    (OAI.AnisotropicCalderon.EnergyBridge.contDiff_vol g hg) hA hθ p hvol hN hcrit
  have hb : ∀ i k, ContDiff ℝ ∞ (fun y => principalCoefficient g y i k) :=
    OAI.AnisotropicCalderon.EnergyBridge.contDiff_principalCoefficient_entry g hg
  have hbs : ∀ i k, (fun y => principalCoefficient g y i k) =
      fun y => principalCoefficient g y k i := by
    intro i k
    funext y
    simp only [principalCoefficient, Matrix.smul_apply, smul_eq_mul]
    rw [congrFun (hsymm i k) y]
  exact local_strict_weight_carleman_of_point_strictness hb hbs hθ p hNb hcritb

end OAI.AnisotropicCalderon.StrictWeightCarleman
end
