import Calderon.MetricCoefficient
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option maxSynthPendingDepth 10

noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge

theorem contDiff_matrix_det_of_entries (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) :
    ContDiff ℝ ∞ (fun x => (g x).det) := by
  classical
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul
    (contDiff_prod (fun i _ => hs (σ i) i)))

theorem contDiff_metric (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ g :=
  contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => hg.smooth i j))

theorem contDiff_metric_det (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (fun x => (g x).det) :=
  contDiff_matrix_det_of_entries g hg.smooth

theorem contDiff_metric_adjugate_entry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => (g x).adjugate i j) := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_matrix_det_of_entries (fun x => (g x).updateRow j (Pi.single i 1))
  intro l m
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa [Matrix.updateRow_apply, hl] using hg.smooth l m

theorem contDiff_metric_inverse_entry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => (g x)⁻¹ i j) := by
  have hd : ContDiff ℝ ∞ (fun x => (g x).det⁻¹) :=
    (contDiff_metric_det g hg).inv (fun x => ne_of_gt (hg.posDef x).det_pos)
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.mul (contDiff_metric_adjugate_entry g hg i j)

theorem contDiff_metric_inverse (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (fun x => (g x)⁻¹) :=
  contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => contDiff_metric_inverse_entry g hg i j))

theorem contDiff_vol (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (vol g) :=
  (contDiff_metric_det g hg).sqrt (fun x => ne_of_gt (hg.posDef x).det_pos)

theorem contDiff_principalCoefficient_entry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => principalCoefficient g x i j) := by
  exact (contDiff_vol g hg).mul (contDiff_metric_inverse_entry g hg i j)

theorem contDiff_principalCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (principalCoefficient g) :=
  contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => contDiff_principalCoefficient_entry g hg i j))

theorem vol_eq_one_of_exterior (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x : R3) (hx : 1 ≤ ‖x‖) : vol g x = 1 := by
  simp [vol, hg.euclidean_exterior x hx]

theorem principalCoefficient_eq_one_of_exterior (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x : R3) (hx : 1 ≤ ‖x‖) : principalCoefficient g x = 1 := by
  simp [principalCoefficient, hg.euclidean_exterior x hx, vol_eq_one_of_exterior g hg x hx]

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.contDiff_metric_inverse
#print axioms OAI.AnisotropicCalderon.EnergyBridge.contDiff_vol
#print axioms OAI.AnisotropicCalderon.EnergyBridge.contDiff_principalCoefficient
