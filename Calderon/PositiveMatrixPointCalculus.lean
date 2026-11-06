import Calderon.WeightedMatrixCalculus

set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator

theorem contDiffAt_positiveMatrix_inverse_entry (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.PosDef) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun G : Matrix (Fin 3) (Fin 3) ℝ => G⁻¹ i j) A := by
  have hd : ContDiffAt ℝ ∞ (fun G : Matrix (Fin 3) (Fin 3) ℝ => G.det⁻¹) A :=
    (contDiff_matrixFamily_det id contDiff_id).contDiffAt.inv (ne_of_gt hA.det_pos)
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
  exact hd.mul (contDiff_matrixFamily_adjugate_entry id contDiff_id i j).contDiffAt

theorem contDiffAt_positiveMatrix_inverse (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) :
    ContDiffAt ℝ ∞ (fun G : Matrix (Fin 3) (Fin 3) ℝ => G⁻¹) A :=
  contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr
    (fun j => contDiffAt_positiveMatrix_inverse_entry A hA i j))

theorem contDiffAt_positiveMatrix_volumeDensity (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.PosDef) : ContDiffAt ℝ ∞ (matrixVolumeDensity id) A :=
  (contDiff_matrixFamily_det id contDiff_id).contDiffAt.sqrt (ne_of_gt hA.det_pos)

theorem contDiffAt_positiveMatrix_principalCoefficient (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.PosDef) : ContDiffAt ℝ ∞ (matrixPrincipalCoefficient id) A :=
  (contDiffAt_positiveMatrix_volumeDensity A hA).smul (contDiffAt_positiveMatrix_inverse A hA)

theorem hasDerivAt_matrixVolumeDensity_zero (G : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℝ) (hG : HasDerivAt G 0 r) (hpos : (G r).PosDef) :
    HasDerivAt (matrixVolumeDensity G) 0 r := by
  have hd := ((contDiffAt_positiveMatrix_volumeDensity (G r) hpos).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt r hG
  simp only [map_zero] at hd
  change HasDerivAt (matrixVolumeDensity G) 0 r at hd
  exact hd

theorem hasDerivAt_matrixPrincipalCoefficient_zero (G : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℝ) (hG : HasDerivAt G 0 r) (hpos : (G r).PosDef) :
    HasDerivAt (matrixPrincipalCoefficient G) 0 r := by
  have hd := ((contDiffAt_positiveMatrix_principalCoefficient (G r) hpos).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt r hG
  simp only [map_zero] at hd
  change HasDerivAt (matrixPrincipalCoefficient G) 0 r at hd
  exact hd
end OAI.AnisotropicCalderon.MetricOperator
