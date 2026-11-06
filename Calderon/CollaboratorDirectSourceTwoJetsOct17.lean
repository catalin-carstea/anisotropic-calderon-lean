import Calderon.CollaboratorSourceJetWeakEstimatesOct17
import Calderon.RadiusTwoAdmissibleSourceJets
import Calderon.SourceRungeTargetGeometry

/-! Direct actual-metric source two-jets from L² Runge and interior estimates.
The generic H5 source Runge proposition and DC.main are not premises. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily MetricVolume Literature TauCeti TauCeti.PDE Regularity
open _root_.OAI.AnisotropicCalderon.Affine

/-- Approximate the actual two-jet of an actual local homogeneous solution. -/
theorem exists_radiusTwoSmoothSource_twoJet_approx_of_localSolution
    (hUCP : UniqueContinuation) (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1 / 8 : ℝ))
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (w : R3 → ℝ)
    (hw : ContDiffOn ℝ ∞ w (ball p ρ₀))
    (hwe : ∀ x ∈ ball p ρ₀, divCoeffGrad (principalCoefficient g) w x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      ‖((radiusTwoSmoothSourceResponse hreg hcalc g hg f p,
          (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p,
            fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p)) :
          RadiusTwoRawTwoJet) - (w p, (fderiv ℝ w p, fderiv ℝ (fderiv ℝ w) p))‖ < ε := by
  have hA := contDiff_principalCoefficient g hg
  have hpos := principalCoefficient_posDef g hg
  obtain ⟨r, hr, hBig, hDisj, _hConnected⟩ := exists_sourceRunge_target_radius p hp hSource
  let ρ : ℝ := min ρ₀ r
  have hρ : 0 < ρ := lt_min hρ₀ hr
  have hρ₀le : ρ ≤ ρ₀ := min_le_left _ _
  have hρr : ρ ≤ r := min_le_right _ _
  have hρ₁ : 0 < ρ / 2 := by positivity
  have hρ₂ : 0 < ρ / 4 := by positivity
  have hρ₃ : 0 < ρ / 8 := by positivity
  have hSmall : closedBall p (ρ / 2) ⊆ ball (0 : R3) 2 :=
    (closedBall_subset_closedBall (by linarith)).trans hBig
  obtain ⟨v₀, hv₀⟩ := JetsAsm.exists_w1p_of_contDiffOn hρ₁ (by linarith) hw
  have hs₀ : ball p (ρ / 2) ⊆ ball p ρ₀ := ball_subset_ball (by linarith)
  have hv₀w := DC.weak_of_classical p hρ₁ hA v₀ (hw.mono hs₀) hv₀
    (fun x hx => hwe x (hs₀ hx))
  obtain ⟨C, hC, hJetBound⟩ := exists_weak_solution_rawJet_bound p hρ₃
    (by linarith : ρ / 8 < ρ / 4) hA hpos
  let η : ℝ := ε / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hη : 0 < η := div_pos hε hC1
  have hcl : closure (ball p (ρ / 4)) = closedBall p (ρ / 4) := closure_ball p hρ₂.ne'
  obtain ⟨f, hf⟩ := l2_runge hUCP 0 (by norm_num : (0 : ℝ) < 2) hA hpos
    fixedExteriorSourceOpens_nonempty (fun x hx => fixedExteriorSourceOpens_le_radiusTwo hx)
    (Kresp g hg) (fun f => (radiusTwoSourceSolution g hg _).2)
    (fun f φ hφ => radiusTwoSourceSolution_integral g hg _ φ hφ)
    (U := ball p (ρ / 4)) (U' := ball p (ρ / 2)) isOpen_ball isOpen_ball
    (by rw [hcl]; exact closedBall_subset_ball (by linarith))
    (ball_subset_closedBall.trans hSmall)
    (by
      rw [hcl]
      exact hDisj.mono ball_subset_closedBall (closedBall_subset_closedBall (by linarith)))
    (by
      rw [hcl]
      exact isConnected_ball_diff_one hρ₂
        ((closedBall_subset_closedBall (by linarith)).trans hSmall))
    v₀ hv₀w (pow_pos hη 2)
  have hle₁ : ballO p (ρ / 4) ≤ ballO 0 2 := fun x hx =>
    hSmall (ball_subset_closedBall (ball_subset_ball (by linarith) hx))
  have hle₂ : ballO p (ρ / 4) ≤ ballO p (ρ / 2) := fun x hx =>
    ball_subset_ball (by linarith) hx
  have hf0 : ∀ x ∈ ball p (ρ / 4), (f : R3 → ℝ) x = 0 := by
    intro x hx
    exact RungeAux.eq_zero_of_notMem f fun hxW =>
      (Set.disjoint_left.mp hDisj) (ball_subset_closedBall hxW)
        (ball_subset_closedBall (ball_subset_ball (by linarith) hx))
  have hKz := radiusTwoSourceSolution_restrict_weak_zero_of_source_zero
    g hg (ballO p (ρ / 4)) hle₁ f hf0
  have hD := sub_weak_zero p (ρ / 4) hA.continuous hKz
    (restrict_weak_zero hle₂ (principalCoefficient g) hv₀w)
  have hval : ⇑(W1p.value (W1p.restrictL hle₁ (Kresp g hg f) - W1p.restrictL hle₂ v₀))
      =ᵐ[(volume : Measure R3).restrict (ball p (ρ / 4))]
      fun x => W1p.value (Kresp g hg f) x - W1p.value v₀ x := by
    have hsub : W1p.value (W1p.restrictL hle₁ (Kresp g hg f) - W1p.restrictL hle₂ v₀) =
        W1p.value (W1p.restrictL hle₁ (Kresp g hg f)) - W1p.value (W1p.restrictL hle₂ v₀) := by
      simp only [← W1p.valueL_apply, map_sub]
    rw [hsub]
    filter_upwards [Lp.coeFn_sub (W1p.value (W1p.restrictL hle₁ (Kresp g hg f)))
      (W1p.value (W1p.restrictL hle₂ v₀)), W1p.value_restrictL_ae hle₁ (Kresp g hg f),
      W1p.value_restrictL_ae hle₂ v₀] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hNorm : ‖W1p.value (W1p.restrictL hle₁ (Kresp g hg f) - W1p.restrictL hle₂ v₀)‖ < η :=
    norm_lt_of_ae_integral_sq_lt (ballO p (ρ / 4)) _ _ hval hη.le hf
  let response := radiusTwoSmoothSourceResponse hreg hcalc g hg
  have hresp : IsRadiusTwoSmoothSourceResponse g hg response :=
    isRadiusTwoSmoothSourceResponse_radiusTwoSmoothSourceResponse hreg hcalc g hg
  have hs₁ : ball p (ρ / 8) ⊆ ball (0 : R3) 2 :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hSmall)
  have hs₂ : ball p (ρ / 8) ⊆ ball p ρ₀ := ball_subset_ball (by linarith)
  have hSmooth : ContDiffOn ℝ ∞ (fun x => response f x - w x) (ball p (ρ / 8)) :=
    ((hresp f).1.mono hs₁).sub (hw.mono hs₂)
  have hRep : ⇑(W1p.value (W1p.restrictL hle₁ (Kresp g hg f) - W1p.restrictL hle₂ v₀))
      =ᵐ[(volume : Measure R3).restrict (ball p (ρ / 8))]
      fun x => response f x - w x := by
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith) : ball p (ρ / 8) ⊆ ball p (ρ / 4)) hval
    have h2 := ae_restrict_of_ae_restrict_of_subset hs₁ (hresp f).2.2.1
    have h3 := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith) : ball p (ρ / 8) ⊆ ball p (ρ / 2)) hv₀
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    change response f x = W1p.value (Kresp g hg f) x at hx2
    rw [hx1, ← hx2, hx3]
  have hJ := hJetBound _ hD _ hSmooth hRep
  change ‖Jets.jet (fun x => response f x - w x) p‖ ≤ C *
    ‖W1p.value (W1p.restrictL hle₁ (Kresp g hg f) - W1p.restrictL hle₂ v₀)‖ at hJ
  rw [JetsAsm.jet_sub
    (Jets.contDiffAt_two_of_ball (hresp f).1 hp)
    (Jets.contDiffAt_two_of_ball hw (mem_ball_self hρ₀))] at hJ
  refine ⟨f, ?_⟩
  change ‖Jets.jet (response f) p - Jets.jet w p‖ < ε
  calc
    ‖Jets.jet (response f) p - Jets.jet w p‖ ≤ C *
        ‖W1p.value (W1p.restrictL hle₁ (Kresp g hg f) - W1p.restrictL hle₂ v₀)‖ := hJ
    _ ≤ (C + 1) *
        ‖W1p.value (W1p.restrictL hle₁ (Kresp g hg f) - W1p.restrictL hle₂ v₀)‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (C + 1) * η := mul_lt_mul_of_pos_left hNorm hC1
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hC1)

/-- The original exact native admissible source-jet range, via the smaller-ball route. -/
theorem radiusTwoSmoothSourceJetLinear_range_eq_admissible_of_uniqueContinuation
    (hUCP : UniqueContinuation) (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1 / 8 : ℝ)) :
    LinearMap.range (radiusTwoSmoothSourceJetLinear hreg hcalc g hg p hp) =
      radiusTwoAdmissibleRawJets g p := by
  have hOutside : p ∉ (fixedExteriorSourceOpens : Set R3) :=
    fun h => hSource (ball_subset_closedBall h)
  apply SourceJet.range_eq_of_approx
    (radiusTwoSmoothSourceJetLinear hreg hcalc g hg p hp) (radiusTwoAdmissibleRawJets g p)
    (range_radiusTwoSmoothSourceJetLinear_le_admissible hreg hcalc g hg p hp hOutside)
  intro j hj ε hε
  have hA := contDiff_principalCoefficient g hg
  have hpos := principalCoefficient_posDef g hg
  obtain ⟨ρ₀, hρ₀, hloc⟩ := exists_local_solution_jet hA hpos p
  have hCompat : jetFunctional (principalCoefficient g) p j.2.1 j.2.2 = 0 := by
    have hPDE : nativeMetricJetFunctional g p j.2.1 j.2.2 = 0 := hj.2
    change -(jetFunctional (principalCoefficient g) p j.2.1 j.2.2) = 0 at hPDE
    exact neg_eq_zero.mp hPDE
  obtain ⟨w, hw, hwe, ha, hξ, hH⟩ := hloc j.1 j.2.1 j.2.2 hj.1 hCompat
  have hwj : ((w p, (fderiv ℝ w p, fderiv ℝ (fderiv ℝ w) p)) : RadiusTwoRawTwoJet) = j := by
    rw [ha, hξ, hH]
  obtain ⟨f, hf⟩ := exists_radiusTwoSmoothSource_twoJet_approx_of_localSolution
    hUCP hreg hcalc g hg p hp hSource hρ₀ w hw hwe hε
  refine ⟨f, ?_⟩
  change ‖((radiusTwoSmoothSourceResponse hreg hcalc g hg f p,
    (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p,
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p)) :
        RadiusTwoRawTwoJet) - j‖ < ε
  rw [← hwj]
  exact hf

/-- The same concrete prescribed value, covector and Hessian conclusion. -/
theorem exists_radiusTwoSmoothSource_prescribed_twoJet_of_uniqueContinuation
    (hUCP : UniqueContinuation) (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1 / 8 : ℝ))
    (a : ℝ) (ξ : R3 →L[ℝ] ℝ) (H : R3 →L[ℝ] (R3 →L[ℝ] ℝ))
    (hSym : ∀ v w : R3, H v w = H w v) (hPDE : nativeMetricJetFunctional g p ξ H = 0) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse hreg hcalc g hg f p = a ∧
      fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p = ξ ∧
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f)) p = H := by
  have hMem : (a, (ξ, H)) ∈ radiusTwoAdmissibleRawJets g p := ⟨hSym, hPDE⟩
  rw [← radiusTwoSmoothSourceJetLinear_range_eq_admissible_of_uniqueContinuation
    hUCP hreg hcalc g hg p hp hSource] at hMem
  obtain ⟨f, hf⟩ := hMem
  exact ⟨f, congrArg Prod.fst hf, congrArg (fun j : RadiusTwoRawTwoJet => j.2.1) hf,
    congrArg (fun j : RadiusTwoRawTwoJet => j.2.2) hf⟩

end OAI.AnisotropicCalderon.ExteriorSource
