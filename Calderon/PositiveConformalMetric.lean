import Calderon.MetricSmooth
import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge

lemma contDiff_matrix_adjugate_entry (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => (g x).adjugate i j) := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_matrix_det_of_entries (fun x => (g x).updateRow j (Pi.single i 1))
  intro l m
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa [Matrix.updateRow_apply, hl] using hs l m

lemma contDiff_matrix_inverse_entry (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => (g x)⁻¹ i j) := by
  have hd : ContDiff ℝ ∞ (fun x => (g x).det⁻¹) :=
    (contDiff_matrix_det_of_entries g hs).inv (fun x => ne_of_gt (hp x).det_pos)
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.mul (contDiff_matrix_adjugate_entry g hs i j)

lemma contDiff_inverse_of_smooth_posDef (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef) :
    ContDiff ℝ ∞ (fun x => (g x)⁻¹) :=
  contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => contDiff_matrix_inverse_entry g hs hp i j))

lemma contDiff_vol_of_smooth_posDef (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef) :
    ContDiff ℝ ∞ (vol g) :=
  (contDiff_matrix_det_of_entries g hs).sqrt (fun x => ne_of_gt (hp x).det_pos)

lemma vol_pos_of_posDef (g : MatrixField) (hp : ∀ x, (g x).PosDef) (x : R3) :
    0 < vol g x := Real.sqrt_pos.mpr (hp x).det_pos

lemma contDiff_principalCoefficient_of_smooth_posDef (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef) :
    ContDiff ℝ ∞ (principalCoefficient g) :=
  contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
    (contDiff_vol_of_smooth_posDef g hs hp).mul (contDiff_matrix_inverse_entry g hs hp i j)))

/-- Exact conformal scalar multiplication, with no exterior-flatness assertion. -/
def conformalMatrix (g : MatrixField) (f : R3 → ℝ) : MatrixField :=
  fun x => Real.exp (2 * f x) • g x

lemma conformalMatrix_smooth_entries (g : MatrixField) (f : R3 → ℝ)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => conformalMatrix g f x i j) :=
  (Real.contDiff_exp.comp (contDiff_const.mul hf)).mul (hs i j)

lemma conformalMatrix_posDef (g : MatrixField) (f : R3 → ℝ)
    (hp : ∀ x, (g x).PosDef) (x : R3) : (conformalMatrix g f x).PosDef :=
  (hp x).smul (Real.exp_pos _)

lemma conformalMatrix_inverse (g : MatrixField) (f : R3 → ℝ)
    (hp : ∀ x, (g x).PosDef) (x : R3) :
    (conformalMatrix g f x)⁻¹ = Real.exp (-2 * f x) • (g x)⁻¹ := by
  letI : Invertible (Real.exp (2 * f x)) := invertibleOfNonzero (Real.exp_ne_zero _)
  have h := Matrix.inv_smul (g x) (Real.exp (2 * f x))
    ((isUnit_iff_ne_zero).mpr (ne_of_gt (hp x).det_pos))
  simpa only [conformalMatrix, invOf_eq_inv, Real.exp_neg, neg_mul] using h

lemma vol_conformalMatrix (g : MatrixField) (f : R3 → ℝ) (x : R3) :
    vol (conformalMatrix g f) x = Real.exp (3 * f x) * vol g x := by
  unfold vol conformalMatrix
  rw [Matrix.det_smul, Fintype.card_fin,
    Real.sqrt_mul (pow_nonneg (Real.exp_nonneg _) _) _]
  have he : Real.exp (2 * f x) ^ 3 = Real.exp (3 * f x) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma principalCoefficient_conformalMatrix (g : MatrixField) (f : R3 → ℝ)
    (hp : ∀ x, (g x).PosDef) (x : R3) :
    principalCoefficient (conformalMatrix g f) x = Real.exp (f x) • principalCoefficient g x := by
  unfold principalCoefficient
  rw [vol_conformalMatrix, conformalMatrix_inverse g f hp]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  have he : Real.exp (3 * f x) * Real.exp (-2 * f x) = Real.exp (f x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (3 * f x) * Real.exp (-2 * f x)) * (vol g x * (g x)⁻¹ i j) := by ring
    _ = _ := by rw [he]

lemma contDiff_conformalMatrix_inverse (g : MatrixField) (f : R3 → ℝ)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => (conformalMatrix g f x)⁻¹) :=
  contDiff_inverse_of_smooth_posDef _ (conformalMatrix_smooth_entries g f hs hf)
    (conformalMatrix_posDef g f hp)

lemma contDiff_vol_conformalMatrix (g : MatrixField) (f : R3 → ℝ)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (vol (conformalMatrix g f)) :=
  contDiff_vol_of_smooth_posDef _ (conformalMatrix_smooth_entries g f hs hf)
    (conformalMatrix_posDef g f hp)

lemma contDiff_principalCoefficient_conformalMatrix (g : MatrixField) (f : R3 → ℝ)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (principalCoefficient (conformalMatrix g f)) :=
  contDiff_principalCoefficient_of_smooth_posDef _ (conformalMatrix_smooth_entries g f hs hf)
    (conformalMatrix_posDef g f hp)

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.contDiff_inverse_of_smooth_posDef
#print axioms OAI.AnisotropicCalderon.EnergyBridge.contDiff_vol_of_smooth_posDef
#print axioms OAI.AnisotropicCalderon.EnergyBridge.conformalMatrix_inverse
#print axioms OAI.AnisotropicCalderon.EnergyBridge.vol_conformalMatrix
#print axioms OAI.AnisotropicCalderon.EnergyBridge.principalCoefficient_conformalMatrix
