import Calderon.NormalizedMetricMatrix
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def matrixVolumeDensity (G : P → Matrix (Fin 3) (Fin 3) ℝ) (p : P) : ℝ :=
  Real.sqrt (G p).det

def matrixPrincipalCoefficient (G : P → Matrix (Fin 3) (Fin 3) ℝ) (p : P) :
    Matrix (Fin 3) (Fin 3) ℝ := matrixVolumeDensity G p • (G p)⁻¹

theorem contDiff_matrixFamily_det (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (fun p => (G p).det) := by
  classical
  have he := contDiff_pi.mp hG
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul
    (contDiff_prod (fun i _ => contDiff_pi.mp (he (σ i)) i)))

theorem contDiff_matrixFamily_adjugate_entry (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ContDiff ℝ ∞ G) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p => (G p).adjugate i j) := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_matrixFamily_det (fun p => (G p).updateRow j (Pi.single i 1))
  apply contDiff_pi.mpr
  intro l
  apply contDiff_pi.mpr
  intro m
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow_apply,hl,if_false] using
      contDiff_pi.mp (contDiff_pi.mp hG l) m

theorem contDiff_matrixFamily_inverse_entry (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ContDiff ℝ ∞ G) (hpos : ∀ p, (G p).PosDef) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p => (G p)⁻¹ i j) := by
  have hd : ContDiff ℝ ∞ (fun p => (G p).det⁻¹) :=
    (contDiff_matrixFamily_det G hG).inv (fun p => ne_of_gt (hpos p).det_pos)
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
  exact hd.mul (contDiff_matrixFamily_adjugate_entry G hG i j)

theorem contDiff_matrixFamily_inverse (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ContDiff ℝ ∞ G) (hpos : ∀ p, (G p).PosDef) :
    ContDiff ℝ ∞ (fun p => (G p)⁻¹) :=
  contDiff_pi.mpr (fun i => contDiff_pi.mpr
    (fun j => contDiff_matrixFamily_inverse_entry G hG hpos i j))

theorem contDiff_matrixVolumeDensity (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ContDiff ℝ ∞ G) (hpos : ∀ p, (G p).PosDef) :
    ContDiff ℝ ∞ (matrixVolumeDensity G) :=
  (contDiff_matrixFamily_det G hG).sqrt (fun p => ne_of_gt (hpos p).det_pos)

theorem contDiff_matrixPrincipalCoefficient (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hG : ContDiff ℝ ∞ G) (hpos : ∀ p, (G p).PosDef) :
    ContDiff ℝ ∞ (matrixPrincipalCoefficient G) :=
  (contDiff_matrixVolumeDensity G hG hpos).smul (contDiff_matrixFamily_inverse G hG hpos)

theorem matrixVolumeDensity_pos (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hpos : ∀ p, (G p).PosDef) (p : P) : 0 < matrixVolumeDensity G p :=
  Real.sqrt_pos.mpr (hpos p).det_pos

theorem matrixPrincipalCoefficient_posDef (G : P → Matrix (Fin 3) (Fin 3) ℝ)
    (hpos : ∀ p, (G p).PosDef) (p : P) : (matrixPrincipalCoefficient G p).PosDef :=
  (hpos p).inv.smul (matrixVolumeDensity_pos G hpos p)
end OAI.AnisotropicCalderon.MetricOperator
