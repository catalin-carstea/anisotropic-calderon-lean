import Calderon.RadiusTwoSourcePoleCutoffEnergy

/-! Full EXPANSION.json precedes this genuine zero-space cutoff graph estimate. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Gradient ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoSource_poleCutoff_graph_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ lam Lam : ℝ, 0 < lam ∧ 0 ≤ Lam ∧
      ∀ (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ), HasCompactSupport χ →
      ∀ (M : ℝ) (hM : 0 ≤ M) (hAbs : ∀ x : R3, |χ x| ≤ M)
        (hGrad : ∀ x : R3, ‖gradient χ x‖ ≤ M) (f : RadiusTwoL2),
      (∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, χ x * f x = 0) →
      let u : RadiusTwoH1 := (radiusTwoSourceSolution g hg f : RadiusTwoH1)
      let w : RadiusTwoH1 := TauCeti.W1p.contDiffSMul χ hχ hM
        (fun x _ => hAbs x) (fun x _ => hGrad x) u
      w ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 ∧
        ‖w‖ ^ 2 ≤ M ^ 2 * (3 + 2 * (2 * Lam / lam) ^ 2) * ‖TauCeti.W1p.value u‖ ^ 2 := by
  obtain ⟨lam,Lam,hlam,hLam,hEnergy⟩ := exists_radiusTwoSource_poleCutoff_energy_bound g hg
  refine ⟨lam,Lam,hlam,hLam,?_⟩
  intro χ hχ hCompact M hM hAbs hGrad f hχf
  let u : RadiusTwoH1 := (radiusTwoSourceSolution g hg f : RadiusTwoH1)
  let w : RadiusTwoH1 := TauCeti.W1p.contDiffSMul χ hχ hM
    (fun x _ => hAbs x) (fun x _ => hGrad x) u
  refine ⟨TauCeti.W1p.contDiffSMul_mem_w1p0Submodule hχ hM
    (fun x _ => hAbs x) (fun x _ => hGrad x) (radiusTwoSourceSolution g hg f).property,?_⟩
  have hValue : ‖TauCeti.W1p.value w‖ ^ 2 ≤ M ^ 2 * ‖TauCeti.W1p.value u‖ ^ 2 := by
    calc
      _ = ∫ x in radiusTwoOpens, TauCeti.W1p.value w x ^ 2 ∂(volume : Measure R3) :=
        (TauCeti.W1p.integral_value_sq_eq_norm_value_sq w).symm
      _ ≤ ∫ x in radiusTwoOpens, M ^ 2 * TauCeti.W1p.value u x ^ 2
          ∂(volume : Measure R3) := by
        apply integral_mono_ae (TauCeti.W1p.integrable_value_sq w)
          ((TauCeti.W1p.integrable_value_sq u).const_mul (M ^ 2))
        filter_upwards [TauCeti.W1p.value_contDiffSMul_ae hχ hM
          (fun x _ => hAbs x) (fun x _ => hGrad x) u] with x hx
        have hχsq : χ x ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs (χ x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hAbs x) 2
        dsimp only [w]
        rw [hx,smul_eq_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right hχsq (sq_nonneg _)
      _ = M ^ 2 * ‖TauCeti.W1p.value u‖ ^ 2 := by
        rw [integral_const_mul,TauCeti.W1p.integral_value_sq_eq_norm_value_sq]
  have hWeighted :
      (∫ x in radiusTwoOpens, ‖gradient χ x‖ ^ 2 * TauCeti.W1p.value u x ^ 2
        ∂(volume : Measure R3)) ≤ M ^ 2 * ‖TauCeti.W1p.value u‖ ^ 2 := by
    have h := TauCeti.PDE.W1p.setIntegral_norm_gradient_sq_mul_value_sq_le u hχ
      (G := M) hGrad (S := Set.univ) MeasurableSet.univ (subset_univ _)
      (TauCeti.W1p.integrable_value_sq u) (Filter.Eventually.of_forall (fun _ => le_rfl))
    simpa only [Set.inter_univ,TauCeti.W1p.integral_value_sq_eq_norm_value_sq] using h
  have hGradValue : ‖TauCeti.W1p.gradient w‖ ^ 2 ≤
      (2 * (2 * Lam / lam) ^ 2 + 2) * (M ^ 2 * ‖TauCeti.W1p.value u‖ ^ 2) := by
    calc
      _ ≤ 2 * (∫ x in radiusTwoOpens, χ x ^ 2 * ‖TauCeti.W1p.gradient u x‖ ^ 2
            ∂(volume : Measure R3)) +
          2 * (∫ x in radiusTwoOpens, ‖gradient χ x‖ ^ 2 * TauCeti.W1p.value u x ^ 2
            ∂(volume : Measure R3)) :=
        TauCeti.W1p.norm_gradient_contDiffSMul_sq_le hχ hM
          (fun x _ => hAbs x) (fun x _ => hGrad x) u
      _ ≤ 2 * ((2 * Lam / lam) ^ 2 *
          ∫ x in radiusTwoOpens, ‖gradient χ x‖ ^ 2 * TauCeti.W1p.value u x ^ 2
            ∂(volume : Measure R3)) +
          2 * (∫ x in radiusTwoOpens, ‖gradient χ x‖ ^ 2 * TauCeti.W1p.value u x ^ 2
            ∂(volume : Measure R3)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hEnergy f χ hχ hCompact hχf) (by norm_num)) le_rfl
      _ = (2 * (2 * Lam / lam) ^ 2 + 2) *
          (∫ x in radiusTwoOpens, ‖gradient χ x‖ ^ 2 * TauCeti.W1p.value u x ^ 2
            ∂(volume : Measure R3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWeighted (by positivity)
  calc
    ‖w‖ ^ 2 = ‖TauCeti.W1p.value w‖ ^ 2 + ‖TauCeti.W1p.gradient w‖ ^ 2 :=
      TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq w
    _ ≤ M ^ 2 * ‖TauCeti.W1p.value u‖ ^ 2 +
        (2 * (2 * Lam / lam) ^ 2 + 2) * (M ^ 2 * ‖TauCeti.W1p.value u‖ ^ 2) :=
      add_le_add hValue hGradValue
    _ = M ^ 2 * (3 + 2 * (2 * Lam / lam) ^ 2) * ‖TauCeti.W1p.value u‖ ^ 2 := by ring

end OAI.AnisotropicCalderon.ExteriorSource
