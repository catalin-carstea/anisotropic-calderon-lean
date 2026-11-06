import Calderon.ReferenceCovariantJets

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.RadiusProfile

def coordinateProductTensor (n : ℕ) (I : Fin n → Fin 3) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ).compContinuousLinearMap
    (fun j => EuclideanSpace.proj (𝕜 := ℝ) (I j))

lemma coordinateProductTensor_apply (n : ℕ) (I : Fin n → Fin 3) (V : Fin n → R3) :
    coordinateProductTensor n I V = ∏ j, (V j) (I j) := by
  simp [coordinateProductTensor, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]

lemma norm_coordinateProductTensor_le (n : ℕ) (I : Fin n → Fin 3) :
    ‖coordinateProductTensor n I‖ ≤ 1 := by
  have hproj : ∀ i : Fin 3, ‖(EuclideanSpace.proj (𝕜 := ℝ) i : R3 →L[ℝ] ℝ)‖ ≤ 1 := by
    intro i
    refine (EuclideanSpace.proj (𝕜 := ℝ) i : R3 →L[ℝ] ℝ).opNorm_le_bound (by norm_num) ?_
    intro V
    change ‖V i‖ ≤ 1 * ‖V‖
    simpa only [one_mul] using (PiLp.norm_apply_le V i)
  have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ)
    (fun j => EuclideanSpace.proj (𝕜 := ℝ) (I j))
  simp only [ContinuousMultilinearMap.norm_mkPiAlgebraFin, one_mul] at h
  exact h.trans (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hproj (I j)))

lemma coordinateProductTensor_basis (n : ℕ) (I J : Fin n → Fin 3) :
    coordinateProductTensor n I (fun j => jetBasisVector (J j)) = if I = J then 1 else 0 := by
  classical
  rw [coordinateProductTensor_apply]
  by_cases h : I = J
  · subst I
    simp [jetBasisVector]
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [jetBasisVector, hj]

def covariantCoordinateTensor (Γ : CoordinateConnectionFamily) (f : R3 → ℝ)
    (lam : ℝ) (n : ℕ) (x : R3) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ :=
  ∑ I : Fin n → Fin 3, covariantCoordinateJet Γ f lam n x I • coordinateProductTensor n I

lemma covariantCoordinateTensor_basis (Γ : CoordinateConnectionFamily) (f : R3 → ℝ)
    (lam : ℝ) (n : ℕ) (x : R3) (J : Fin n → Fin 3) :
    covariantCoordinateTensor Γ f lam n x (fun j => jetBasisVector (J j)) =
      covariantCoordinateJet Γ f lam n x J := by
  classical
  simp [covariantCoordinateTensor, coordinateProductTensor_basis, smul_eq_mul]

lemma norm_covariantCoordinateTensor_le (Γ : CoordinateConnectionFamily) (f : R3 → ℝ)
    (lam : ℝ) (n : ℕ) (x : R3) (A : ℝ)
    (hA : ∀ I : Fin n → Fin 3, |covariantCoordinateJet Γ f lam n x I| ≤ A) :
    ‖covariantCoordinateTensor Γ f lam n x‖ ≤ (3 : ℝ) ^ n * A := by
  classical
  calc
    ‖covariantCoordinateTensor Γ f lam n x‖ ≤
        ∑ I : Fin n → Fin 3,
          ‖covariantCoordinateJet Γ f lam n x I • coordinateProductTensor n I‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _I : Fin n → Fin 3, A := by
      apply Finset.sum_le_sum
      intro I _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (norm_coordinateProductTensor_le n I)
        (abs_nonneg _)).trans (by simpa using hA I)
    _ = (3 : ℝ) ^ n * A := by simp

def tensorFrameSquare (n : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ) (e : Fin 3 → R3) : ℝ :=
  ∑ I : Fin n → Fin 3, (T (fun j => e (I j))) ^ 2

lemma tensorFrameSquare_nonneg (n : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ) (e : Fin 3 → R3) :
    0 ≤ tensorFrameSquare n T e := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma tensorFrameSquare_le (n : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ) (e : Fin 3 → R3)
    (A : ℝ) (hA : 0 ≤ A) (h : ∀ I : Fin n → Fin 3, |T (fun j => e (I j))| ≤ A) :
    tensorFrameSquare n T e ≤ (3 : ℝ) ^ n * A ^ 2 := by
  unfold tensorFrameSquare
  calc
    (∑ I : Fin n → Fin 3, (T (fun j => e (I j))) ^ 2) ≤
        ∑ _I : Fin n → Fin 3, A ^ 2 := by
      apply Finset.sum_le_sum
      intro I _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).mpr (h I)
    _ = _ := by simp

lemma sqrt_tensorFrameSquare_le (n : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ) (e : Fin 3 → R3)
    (A : ℝ) (hA : 0 ≤ A) (h : ∀ I : Fin n → Fin 3, |T (fun j => e (I j))| ≤ A) :
    Real.sqrt (tensorFrameSquare n T e) ≤ Real.sqrt ((3 : ℝ) ^ n) * A := by
  have hs := Real.sqrt_le_sqrt (tensorFrameSquare_le n T e A hA h)
  simpa only [Real.sqrt_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n),
    Real.sqrt_sq hA] using hs

end OAI.AnisotropicCalderon.RadiusProfile

namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile AngularPolynomial MetricOperator ConnectionError

lemma exists_referenceMetric_uniform_quadratic_lower_bound_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, ∀ x ∈ K, ∀ V : R3,
      c * ‖V‖ ^ 2 ≤
        ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x V, V⟫_ℝ := by
  obtain ⟨d, hd, hmetric⟩ := exists_metricOperatorField_global_lower_bound g hg
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn contDiff_referenceCoordinateDepth.continuous.continuousOn
  refine ⟨Real.exp (-2 * L * A) * d, mul_pos (Real.exp_pos _) hd, ?_⟩
  intro lam x hx V
  have hxA : referenceCoordinateDepth x ≤ A := (le_abs_self _).trans (hA x hx)
  have he : Real.exp (-2 * L * A) ≤ Real.exp (-2 * L * referenceCoordinateDepth x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [referenceMetric_operator_eq]
  simp only [smul_apply, real_inner_smul_left]
  change Real.exp (-2 * L * A) * d * ‖V‖ ^ 2 ≤
    Real.exp (-2 * L * referenceCoordinateDepth x) * ⟪metricOperatorField g (lam • x) V, V⟫_ℝ
  simpa only [mul_assoc] using
    mul_le_mul he (hmetric (lam • x) V) (mul_nonneg hd.le (sq_nonneg _))
      (Real.exp_pos _).le

lemma norm_le_sqrt_inv_of_quadratic_unit (M : R3 →L[ℝ] R3) (c : ℝ) (hc : 0 < c)
    (hM : ∀ V : R3, c * ‖V‖ ^ 2 ≤ ⟪M V, V⟫_ℝ)
    (V : R3) (hV : ⟪M V, V⟫_ℝ ≤ 1) : ‖V‖ ≤ Real.sqrt (1 / c) := by
  apply (Real.le_sqrt (norm_nonneg _) (one_div_pos.mpr hc).le).mpr
  exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using (hM V).trans hV)

theorem exists_dilated_referenceRadius_fixed_uniform_covariant_unit_vectors_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ V : Fin n → R3,
        (∀ j, ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x (V j), V j⟫_ℝ ≤ 1) →
        |covariantCoordinateTensor (referenceConnectionFamily g L)
          (fun y => Real.log (referenceRadius δ R p L y)) lam n x V| ≤
          Cn * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ n := by
  obtain ⟨J, hJ, hcomponents⟩ :=
    exists_dilated_referenceRadius_fixed_uniform_covariant_components_bound g hg L hL K hK n hn
  obtain ⟨c, hc, hmetric⟩ :=
    exists_referenceMetric_uniform_quadratic_lower_bound_on_compact g hg L hL K hK
  let D : ℝ := Real.sqrt (1 / c)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  refine ⟨(3 : ℝ) ^ n * J * D ^ n + 1, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx V hV
  let f : R3 → ℝ := fun y => Real.log (referenceRadius δ R p L y)
  let beta : ℝ := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x
  have hbeta : 0 ≤ beta := Real.sqrt_nonneg _
  let T := covariantCoordinateTensor (referenceConnectionFamily g L) f lam n x
  have hT : ‖T‖ ≤ (3 : ℝ) ^ n * (J * beta ^ n) :=
    norm_covariantCoordinateTensor_le _ _ _ _ _ _
      (hcomponents lam hlam δ hδ hδ1 R hR p hp x hx)
  have hnorm : ∀ j, ‖V j‖ ≤ D := fun j =>
    norm_le_sqrt_inv_of_quadratic_unit _ c hc (hmetric lam x hx) (V j) (hV j)
  have hprod : (∏ j, ‖V j‖) ≤ D ^ n := by
    calc
      (∏ j, ‖V j‖) ≤ ∏ _j : Fin n, D :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hnorm j)
      _ = D ^ n := by simp
  have h := (T.le_opNorm V).trans
    (mul_le_mul hT hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity))
  change |T V| ≤ _
  rw [Real.norm_eq_abs] at h
  nlinarith [pow_nonneg hbeta n]

theorem exists_dilated_referenceRadius_fixed_uniform_covariant_frame_norm_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ e : Fin 3 → R3,
        (∀ i, ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x (e i), e i⟫_ℝ ≤ 1) →
        Real.sqrt (tensorFrameSquare n
          (covariantCoordinateTensor (referenceConnectionFamily g L)
            (fun y => Real.log (referenceRadius δ R p L y)) lam n x) e) ≤
          Cn * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ n := by
  obtain ⟨J, hJ, hunit⟩ :=
    exists_dilated_referenceRadius_fixed_uniform_covariant_unit_vectors_bound g hg L hL K hK n hn
  refine ⟨Real.sqrt ((3 : ℝ) ^ n) * J + 1, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx e he
  let f : R3 → ℝ := fun y => Real.log (referenceRadius δ R p L y)
  let beta : ℝ := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x
  have hbeta : 0 ≤ beta := Real.sqrt_nonneg _
  have h := sqrt_tensorFrameSquare_le n
    (covariantCoordinateTensor (referenceConnectionFamily g L) f lam n x) e
    (J * beta ^ n) (by positivity) (fun I =>
      hunit lam hlam δ hδ hδ1 R hR p hp x hx (fun j => e (I j)) (fun j => he (I j)))
  exact h.trans (by nlinarith [pow_nonneg hbeta n])

end OAI.AnisotropicCalderon.ConformalDepth
