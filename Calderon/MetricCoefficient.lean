import Calderon.EnergyBridge

noncomputable section
open MeasureTheory Matrix

namespace OAI.AnisotropicCalderon.EnergyBridge

/-- The exact frozen volume density is strictly positive for every admissible metric. -/
theorem vol_pos (g : MatrixField) (hg : IsAdmissibleMetric g) (x : R3) :
    0 < vol g x := by
  exact Real.sqrt_pos.mpr (hg.posDef x).det_pos

/-- No extra ellipticity or metric premise is needed for the actual coefficient's positivity. -/
theorem principalCoefficient_posDef (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x : R3) : (principalCoefficient g x).PosDef :=
  (hg.posDef x).inv.smul (vol_pos g hg x)

/-- The coefficient quadratic density is pointwise nonnegative, including the zero vector. -/
theorem principalCoefficient_quadratic_nonneg (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x : R3) (ξ : R3) :
    0 ≤ ξ ⬝ᵥ (principalCoefficient g x *ᵥ ξ) := by
  simpa using (principalCoefficient_posDef g hg x).posSemidef.dotProduct_mulVec_nonneg
    (ξ : Fin 3 → ℝ)

/-- Entrywise frozen smoothness gives continuity in the actual finite matrix topology. -/
theorem continuous_metric (g : MatrixField) (hg : IsAdmissibleMetric g) : Continuous g :=
  continuous_pi fun i => continuous_pi fun j => (hg.smooth i j).continuous

/-- The actual matrix inverse is continuous because the admissible determinant never vanishes. -/
theorem continuous_metric_inverse (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous fun x => (g x)⁻¹ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (continuousAt_matrix_inv (g x) _).comp (continuous_metric g hg).continuousAt
  simpa only [Ring.inverse_eq_inv'] using
    (continuousAt_inv₀ (ne_of_gt (hg.posDef x).det_pos) :
      ContinuousAt (Inv.inv : ℝ → ℝ) (g x).det)

/-- The exact volume density is continuous. -/
theorem continuous_vol (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (vol g) :=
  Real.continuous_sqrt.comp (continuous_metric g hg).matrix_det

/-- The density times inverse coefficient is continuous on all of the ambient space. -/
theorem continuous_principalCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (principalCoefficient g) :=
  (continuous_vol g hg).smul (continuous_metric_inverse g hg)

/-- Nonnegativity of the frozen total integral, with no competitor regularity premise. -/
theorem energy_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g) (u : R3 → ℝ) :
    0 ≤ energy g u := by
  rw [energy_eq_energyFormIntegral]
  apply TauCeti.PDE.energyFormIntegral_zero_drift_self_nonneg
  · exact Filter.Eventually.of_forall fun x ξ => principalCoefficient_quadratic_nonneg g hg x ξ
  · exact Filter.Eventually.of_forall fun _ => le_rfl

/-- Nonnegative total infimum, including any empty frozen competitor set. -/
theorem minimalEnergy_nonneg (g : MatrixField) (hg : IsAdmissibleMetric g) (f : R3 → ℝ) :
    0 ≤ minimalEnergy g f := by
  apply Real.sInf_nonneg
  rintro y ⟨u, hu, rfl⟩
  exact energy_nonneg g hg u

/-- A concrete uniform bilinear upper bound on the exact compact closed unit ball. -/
theorem exists_principalCoefficient_upper_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ x ∈ Metric.closedBall (0 : R3) 1,
      ∀ η ξ : R3, |η ⬝ᵥ (principalCoefficient g x *ᵥ ξ)| ≤ Λ * ‖η‖ * ‖ξ‖ := by
  have hcont : Continuous fun x => ‖TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)‖ :=
    (continuous_norm (E := R3 →L[ℝ] R3 →L[ℝ] ℝ)).comp
      (TauCeti.PDE.continuous_matrixBilinearForm.comp (continuous_principalCoefficient g hg))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : R3) 1).bddAbove_image hcont.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx η ξ
  have hb : ‖TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)‖ ≤ max M 1 :=
    (hM (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  calc
    |η ⬝ᵥ (principalCoefficient g x *ᵥ ξ)| =
        ‖TauCeti.PDE.matrixBilinearForm (principalCoefficient g x) η ξ‖ := by
      rw [TauCeti.PDE.matrixBilinearForm_apply, Real.norm_eq_abs]
    _ ≤ ‖TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)‖ * ‖η‖ * ‖ξ‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ max M 1 * ‖η‖ * ‖ξ‖ := by gcongr

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.principalCoefficient_posDef
#print axioms OAI.AnisotropicCalderon.EnergyBridge.continuous_principalCoefficient
#print axioms OAI.AnisotropicCalderon.EnergyBridge.energy_nonneg
#print axioms OAI.AnisotropicCalderon.EnergyBridge.minimalEnergy_nonneg

#print axioms OAI.AnisotropicCalderon.EnergyBridge.exists_principalCoefficient_upper_bound
