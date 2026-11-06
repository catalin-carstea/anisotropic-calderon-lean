import Calderon.MetricInverseDifferential
import Calderon.MetricKoszulCoordinates

noncomputable section
open scoped Matrix.Norms.Operator InnerProductSpace
namespace OAI.AnisotropicCalderon.MetricVolume

lemma inverseMetric_symmetric (g : MatrixField) (x : R3) (hp : (g x).PosDef)
    (i j : Fin 3) : (g x)⁻¹ i j = (g x)⁻¹ j i := by
  simpa using (hp.inv.isHermitian.apply j i)

lemma metricDerivative_symmetric (g : MatrixField) (x V : R3)
    (hp : ∀ y, (g y).PosDef) (i j : Fin 3) :
    fderiv ℝ (fun y => g y i j) x V = fderiv ℝ (fun y => g y j i) x V := by
  have he : (fun y => g y i j) = (fun y => g y j i) := by
    funext y
    simpa using ((hp y).isHermitian.apply j i)
  rw [he]

lemma symmetric_koszul_contraction (Q : Fin 3 → Fin 3 → ℝ) (D : Fin 3 → Fin 3 → Fin 3 → ℝ) (rho : ℝ)
    (hQ : ∀ i j, Q i j = Q j i) (hD : ∀ i a b, D i a b = D i b a)
    (j : Fin 3) :
    (∑ i : Fin 3, (((rho / 2) * (∑ a : Fin 3, ∑ b : Fin 3, Q b a * D i a b)) * Q i j -
      rho * (∑ a : Fin 3, ∑ b : Fin 3, Q i a * D i a b * Q b j))) =
    -rho * ∑ a : Fin 3, ∑ b : Fin 3, Q a b * ((1 / 2 : ℝ) *
      ∑ c : Fin 3, Q j c * (D a c b + D b c a - D c b a)) := by
  fin_cases j <;>
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, add_zero, Finset.sum_empty, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  all_goals
    simp only [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin 3) = 1 from rfl,
      show (⟨2, by decide⟩ : Fin 3) = 2 from rfl]
    simp only [hQ 1 0, hQ 2 0, hQ 2 1,
      hD 0 1 0, hD 0 2 0, hD 0 2 1,
      hD 1 1 0, hD 1 2 0, hD 1 2 1,
      hD 2 1 0, hD 2 2 0, hD 2 2 1]
    ring

lemma fderiv_densityInverse_entry (g : MatrixField) (x V : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (i j : Fin 3) :
    fderiv ℝ (fun y => vol g y * (g y)⁻¹ i j) x V =
      ((vol g x / 2) * ∑ a : Fin 3, ∑ b : Fin 3,
        (g x)⁻¹ b a * fderiv ℝ (fun y => g y a b) x V) * (g x)⁻¹ i j -
      vol g x * ∑ a : Fin 3, ∑ b : Fin 3,
        (g x)⁻¹ i a * fderiv ℝ (fun y => g y a b) x V * (g x)⁻¹ b j := by
  have hv : DifferentiableAt ℝ (vol g) x :=
    ((hasFDerivAt_metric_determinant g x hg hp).sqrt hp.det_pos.ne').differentiableAt
  let E : Mat →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hi : DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x :=
    (E.hasFDerivAt.comp x (hasFDerivAt_inverseMetric_matrix g x hg hp)).differentiableAt
  rw [fderiv_fun_mul hv hi]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_vol_apply_entries g x V hg hp, fderiv_inverseMetric_entry_apply g x V hg hp]
  ring

lemma densityInverse_connection_contraction (g : MatrixField) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y, (g y).PosDef) (j : Fin 3) :
    (∑ i : Fin 3, fderiv ℝ (fun y => vol g y * (g y)⁻¹ i j) x (coordinateVector i)) =
      -vol g x * ∑ a : Fin 3, ∑ b : Fin 3,
        (g x)⁻¹ a b * metricChristoffel g x a b j := by
  simp_rw [fderiv_densityInverse_entry g x _ hg (hp x), metricChristoffel_eq g x hg]
  exact symmetric_koszul_contraction (fun a b => ((g x)⁻¹ : Mat) a b)
    (fun i a b => fderiv ℝ (fun y => g y a b) x (coordinateVector i))
    (vol g x) (inverseMetric_symmetric g x (hp x))
    (fun i a b => metricDerivative_symmetric g x (coordinateVector i) hp a b) j

end OAI.AnisotropicCalderon.MetricVolume
