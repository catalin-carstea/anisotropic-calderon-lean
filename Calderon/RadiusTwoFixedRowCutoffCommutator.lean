import Calderon.RadiusTwoFixedRowCutoffForcing
import Calderon.NativeWeakValueSmoothFluxIntegration
import Calderon.RadiusTwoSmoothCutoffEnergyDifference
import Calderon.SmoothMetricCutoffFluxBilinear
import Calderon.RadiusTwoNativeTestDilation

/-! EXPANSION.json precedes the actual full-Ag localized commutator. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

theorem nativeWeakValue_smoothMetricFlux_integration
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData) (u : RadiusTwoH1)
    (φ : 𝓓(radiusTwoOpens, ℝ)) :
    (∫ x in radiusTwoOpens, TauCeti.W1p.value u x *
      (∑ i : Fin 3, fderiv ℝ (φ : R3 → ℝ) x (coordinateVector i) * smoothMetricCutoffFlux g η i x)
        ∂(volume : Measure R3)) +
      (∫ x in radiusTwoOpens, φ x * (smoothMetricCutoffFluxDivergence g hg η).1 x *
        TauCeti.W1p.value u x ∂(volume : Measure R3)) =
      -(∫ x in radiusTwoOpens, φ x * (∑ i : Fin 3, smoothMetricCutoffFlux g η i x *
        ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) ∂(volume : Measure R3)) := by
  let J : Fin 3 → R3 → ℝ := smoothMetricCutoffFlux g η
  let D : R3 → ℝ := (smoothMetricCutoffFluxDivergence g hg η).1
  let L : R3 → ℝ := fun x => ∑ i : Fin 3, fderiv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x
  have hJ (i : Fin 3) : ContDiff ℝ ∞ (J i) := contDiff_smoothMetricCutoffFlux g hg η i
  have hL : Continuous L := by
    have hSmoothL : ContDiff ℝ ∞ L := by
      exact ContDiff.sum (fun i _ =>
        ((φ.contDiff.fderiv_right (by simp)).clm_apply
          (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => coordinateVector i))).mul (hJ i))
    exact hSmoothL.continuous
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict radiusTwoOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ,radiusTwoOpens,TopologicalSpace.Opens.coe_mk] using
      ((measure_mono (show ball (0 : R3) 2 ⊆ closedBall (0 : R3) 2 from ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 2).measure_lt_top)⟩
  have hiF : Integrable (fun x : R3 => TauCeti.W1p.value u x * L x)
      ((volume : Measure R3).restrict radiusTwoOpens) := by
    have hm := memLp_radiusTwo_continuous_mul L hL (Lp.memLp (TauCeti.W1p.value u))
    have hi := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hm
    exact hi.congr (Eventually.of_forall (fun x => mul_comm _ _))
  have hiG : Integrable (fun x : R3 => φ x * D x * TauCeti.W1p.value u x)
      ((volume : Measure R3).restrict radiusTwoOpens) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (memLp_radiusTwo_continuous_mul (fun x : R3 => φ x * D x)
        (φ.continuous.mul (smoothMetricCutoffFluxDivergence g hg η).2.continuous)
        (Lp.memLp (TauCeti.W1p.value u)))
  have hLine (i : Fin 3) (x : R3) : lineDeriv ℝ (J i) x (coordinateVector i) =
      fderiv ℝ (J i) x (coordinateVector i) :=
    ((hJ i).differentiable (by simp) x).lineDeriv_eq_fderiv
  have hIBP := nativeWeakValue_smoothFlux_compactTest_integration radiusTwoOpens u J hJ φ
  calc
    _ = ∫ x in radiusTwoOpens, (TauCeti.W1p.value u x * L x +
        φ x * D x * TauCeti.W1p.value u x) ∂(volume : Measure R3) := (integral_add hiF hiG).symm
    _ = ∫ x in radiusTwoOpens, TauCeti.W1p.value u x *
        (∑ i : Fin 3, (⟪gradient (φ : R3 → ℝ) x,coordinateVector i⟫_ℝ * J i x +
          φ x * lineDeriv ℝ (J i) x (coordinateVector i))) ∂(volume : Measure R3) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      simp only [L,D,smoothMetricCutoffFluxDivergence,J,inner_gradient_left,hLine,
        Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    _ = -(∫ x in radiusTwoOpens, φ x *
        (∑ i : Fin 3, ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ * J i x)
          ∂(volume : Measure R3)) := hIBP
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change φ x * (∑ i : Fin 3, ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ * J i x) =
        φ x * (∑ i : Fin 3, J i x * ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ)
      apply congrArg (fun r : ℝ => φ x * r)
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _

theorem radiusTwoMetricEnergy_cutoff_commutator_eq_forcing
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData)
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η.1 x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient η.1 x‖ ≤ M)
    (u : RadiusTwoH1) (φ : 𝓓(radiusTwoOpens, ℝ)) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL η.1 η.2 hM hAbs hGrad
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (S u) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) -
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        u (S (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) =
      ∫ x in radiusTwoOpens, radiusTwoFixedRowCutoffForcing g hg η u x * φ x
        ∂(volume : Measure R3) := by
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL η.1 η.2 hM hAbs hGrad
  let v : RadiusTwoH1 := (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)
  let J : Fin 3 → R3 → ℝ := smoothMetricCutoffFlux g η
  let D : R3 → ℝ := (smoothMetricCutoffFluxDivergence g hg η).1
  let L : R3 → ℝ := fun x => ∑ i : Fin 3, fderiv ℝ (φ : R3 → ℝ) x (coordinateVector i) * J i x
  let V : R3 → ℝ := fun x => ∑ i : Fin 3, J i x * ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ
  let F : R3 → ℝ := fun x => TauCeti.W1p.value u x * L x
  let G : R3 → ℝ := fun x => φ x * D x * TauCeti.W1p.value u x
  let H : R3 → ℝ := fun x => φ x * V x
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict radiusTwoOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ,radiusTwoOpens,TopologicalSpace.Opens.coe_mk] using
      ((measure_mono (show ball (0 : R3) 2 ⊆ closedBall (0 : R3) 2 from ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 2).measure_lt_top)⟩
  have hL : Continuous L := by
    have hSmoothL : ContDiff ℝ ∞ L := by
      exact ContDiff.sum (fun i _ =>
        ((φ.contDiff.fderiv_right (by simp)).clm_apply
          (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => coordinateVector i))).mul
            (contDiff_smoothMetricCutoffFlux g hg η i))
    exact hSmoothL.continuous
  have hiF : Integrable F ((volume : Measure R3).restrict radiusTwoOpens) := by
    have hi := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (memLp_radiusTwo_continuous_mul L hL (Lp.memLp (TauCeti.W1p.value u)))
    exact hi.congr (Eventually.of_forall (fun x => mul_comm _ _))
  have hiG : Integrable G ((volume : Measure R3).restrict radiusTwoOpens) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (memLp_radiusTwo_continuous_mul (fun x : R3 => φ x * D x)
        (φ.continuous.mul (smoothMetricCutoffFluxDivergence g hg η).2.continuous)
        (Lp.memLp (TauCeti.W1p.value u)))
  have hmV : MemLp V 2 ((volume : Measure R3).restrict radiusTwoOpens) := by
    apply memLp_finsetSum
    intro i hi
    exact memLp_radiusTwo_continuous_mul (J i)
      (contDiff_smoothMetricCutoffFlux g hg η i).continuous
      ((Lp.memLp (TauCeti.W1p.gradient u)).inner_const (coordinateVector i))
  have hiH : Integrable H ((volume : Measure R3).restrict radiusTwoOpens) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (memLp_radiusTwo_continuous_mul (φ : R3 → ℝ) φ.continuous hmV)
  have hSplit : (∫ x in radiusTwoOpens, F x ∂(volume : Measure R3)) +
      (∫ x in radiusTwoOpens, G x ∂(volume : Measure R3)) =
      -(∫ x in radiusTwoOpens, H x ∂(volume : Measure R3)) :=
    nativeWeakValue_smoothMetricFlux_integration g hg η u φ
  have hCross (x : R3) (W : R3) :
      TauCeti.PDE.matrixBilinearForm (principalCoefficient g x) W (gradient η.1 x : R3) =
        ∑ i : Fin 3, J i x * ⟪W,coordinateVector i⟫_ℝ := by
    rw [matrixBilinearForm_smoothMetricCutoffFlux]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [coordinateVector,EuclideanSpace.inner_single_right,one_mul,conj_trivial]
    exact mul_comm _ _
  have hSwap (x : R3) (W : R3) :
      TauCeti.PDE.matrixBilinearForm (principalCoefficient g x) (gradient η.1 x : R3) W =
        ∑ i : Fin 3, J i x * ⟪W,coordinateVector i⟫_ℝ := by
    rw [matrixBilinearForm_smoothMetricCutoffFlux_swap g hg]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [coordinateVector,EuclideanSpace.inner_single_right,one_mul,conj_trivial]
    exact mul_comm _ _
  have hPhiCross (x : R3) : TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
      (gradient (φ : R3 → ℝ) x : R3) (gradient η.1 x : R3) = L x := by
    rw [hCross]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_gradient_left]
    exact mul_comm _ _
  have hv : (TauCeti.W1p.value v : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (φ : R3 → ℝ) := by
    dsimp only [v]
    rw [nativeZeroTestLinear_coe,TauCeti.W1p.value_ofTestFunctionₗ]
    exact TauCeti.testFunctionLp_apply_ae (mu := volume) 2 φ
  have hgv : (TauCeti.W1p.gradient v : R3 → R3)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun x : R3 => gradient (φ : R3 → ℝ) x) := by
    dsimp only [v]
    rw [nativeZeroTestLinear_coe,TauCeti.W1p.gradient_ofTestFunctionₗ]
    exact TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ
  have hDiff := radiusTwoMetricEnergy_smoothCutoff_difference g hg η.1 η.2 hM hAbs hGrad u v
  have hDiff' :
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) (S u) v -
        TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) u (S v) =
      ∫ x in radiusTwoOpens, F x - H x ∂(volume : Measure R3) := by
    apply hDiff.trans
    apply integral_congr_ae
    filter_upwards [hv,hgv] with x hx hgradx
    rw [hx,hgradx,hPhiCross,hSwap]
  have hForce : (∫ x in radiusTwoOpens, radiusTwoFixedRowCutoffForcing g hg η u x * φ x
      ∂(volume : Measure R3)) = (-2 : ℝ) * (∫ x in radiusTwoOpens, H x ∂(volume : Measure R3)) -
        (∫ x in radiusTwoOpens, G x ∂(volume : Measure R3)) := by
    calc
      _ = ∫ x in radiusTwoOpens, ((-2 : ℝ)*H x-G x) ∂(volume : Measure R3) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only [radiusTwoFixedRowCutoffForcing,H,G,V,D,J]
        ring
      _ = _ := by rw [integral_sub (hiH.const_mul (-2 : ℝ)) hiG,integral_const_mul]
  calc
    _ = ∫ x in radiusTwoOpens, F x-H x ∂(volume : Measure R3) := hDiff'
    _ = (∫ x in radiusTwoOpens, F x ∂(volume : Measure R3)) -
        (∫ x in radiusTwoOpens, H x ∂(volume : Measure R3)) := integral_sub hiF hiH
    _ = (-2 : ℝ)*(∫ x in radiusTwoOpens, H x ∂(volume : Measure R3)) -
        (∫ x in radiusTwoOpens, G x ∂(volume : Measure R3)) := by linarith [hSplit]
    _ = _ := hForce.symm

end OAI.AnisotropicCalderon.ExteriorSource
