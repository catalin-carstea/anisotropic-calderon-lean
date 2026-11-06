import Calderon.ActualTwoMetricSymmetricSourceKernels
import Calderon.RadiusTwoLocalizedFiniteRowCutoff
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

lemma radiusTwo_restricted_inverseSourceRow_value_ae
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (p : (radiusTwoOpens : Set R3)) :
    ((MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
        ((volume : Measure R3).restrict radiusTwoOpens) 2 S (K p)) : R3 → ℝ)
      =ᵐ[((volume : Measure R3).restrict radiusTwoOpens).restrict S] G p := by
  have hRestrict := MeasureTheory.LpToLpRestrictCLM_coeFn ℝ S (K p)
  have hKG : (K p : R3 → ℝ)
      =ᵐ[((volume : Measure R3).restrict radiusTwoOpens).restrict S] G p :=
    ((hData.1 p).2.2.1.symm).restrict
  exact hRestrict.trans hKG

lemma radiusTwo_restricted_finiteRow_value_ae
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (m : ℕ) (a : Fin m → ℝ)
    (p : Fin m → (radiusTwoOpens : Set R3)) :
    ((MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
        ((volume : Measure R3).restrict radiusTwoOpens) 2 S
        (∑ i : Fin m, a i • K (p i))) : R3 → ℝ)
      =ᵐ[((volume : Measure R3).restrict radiusTwoOpens).restrict S]
        (fun z => ∑ i : Fin m, a i * G (p i) z) := by
  classical
  have hKG : ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z => ∑ i : Fin m, a i * G (p i) z) := by
    have hi (i : Fin m) : ((a i • K (p i) : RadiusTwoL2) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => a i * G (p i) z) := by
      filter_upwards [Lp.coeFn_smul (a i) (K (p i)), (hData.1 (p i)).2.2.1] with z hz hg
      simpa only [Pi.smul_apply, smul_eq_mul, hg] using hz
    have hSum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin m))
      (fun i => a i • K (p i))
    filter_upwards [hSum, ae_all_iff.mpr hi] with z hz hzi
    exact hz.trans (Finset.sum_congr rfl (fun i _ => hzi i))
  have hRestrict := MeasureTheory.LpToLpRestrictCLM_coeFn ℝ S
    (∑ i : Fin m, a i • K (p i) : RadiusTwoL2)
  exact hRestrict.trans hKG.restrict

lemma norm_sq_radiusTwo_restricted_finiteRow
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (S : Set R3) (hS : MeasurableSet S) (m : ℕ) (a : Fin m → ℝ)
    (p : Fin m → (radiusTwoOpens : Set R3)) :
    ‖MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
      ((volume : Measure R3).restrict radiusTwoOpens) 2 S
      (∑ i : Fin m, a i • K (p i))‖ ^ 2 =
        ∫ z in (radiusTwoOpens : Set R3) ∩ S,
          ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z)^2 ∂(volume : Measure R3) := by
  let v : RadiusTwoL2 := ∑ i : Fin m, a i • K (p i)
  let R : RadiusTwoL2 →L[ℝ]
      Lp ℝ 2 (((volume : Measure R3).restrict radiusTwoOpens).restrict S) :=
    MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ ((volume : Measure R3).restrict radiusTwoOpens) 2 S
  calc
    ‖R v‖ ^ 2 = ∫ z, ‖R v z‖ ^ 2
        ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S) :=
      (Lp.integral_norm_sq_eq_norm_sq (R v)).symm
    _ = ∫ z, ‖v z‖ ^ 2
        ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S) := by
      apply integral_congr_ae
      filter_upwards [MeasureTheory.LpToLpRestrictCLM_coeFn ℝ S v] with z hz
      change ‖R v z‖^2 = ‖v z‖^2
      rw [hz]
    _ = _ := by
      rw [Measure.restrict_restrict hS]
      simp only [v, Real.norm_eq_abs, sq_abs, Set.inter_comm]

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_restricted_inverseSourceRow_value_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_restricted_finiteRow_value_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_sq_radiusTwo_restricted_finiteRow
