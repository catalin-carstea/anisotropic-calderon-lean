import Calderon.ActualChosenCoverFiniteCoercivityGlobalMain
import Calderon.ActualAdjointSmoothMultiplierExtendedCenterJointGainTransferJointRegularity
import Calderon.ActualAdjointSmoothMultiplierCanonicalJointGainTransferJointRegularity
import Calderon.ClassicalHarmonicRestrictionFiniteRank
import Calderon.ActualMixedKernelConstruction
import Calderon.ActualSourcePartnerMetricRecovery
import Calderon.ActualRadiusTwoSourcePartnerSmoothness
import Calderon.ExteriorIdentityHomeomorphExtension
import Calderon.ActualRadiusTwoSourceSeparation
import Calderon.CollaboratorFixedDirichletRegularityOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17

/-! Main assembly through the transfer producer. It uses the finite-rank and
joint-regularity producers and the global construction of the Main assembly; the
source-image step is supplied by the original transfer producer, which takes the
two-sided full physical coercivity estimate as a hypothesis. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.MainAssemblyWithTransferProducer
open EnergyBridge DirichletFamily ExteriorSource ExteriorSource.Literature

/-- The local mixed-kernel construction, with its source-data interface and
quantifier order. -/
theorem local_mixed_kernel_construction :
    MixedKernelConstructionTask.ActualMixedKernelConstructionGoal :=
  MixedKernelConstructionTask.actual_mixed_kernel_exists

section FiniteRankRestrictionIntegration
open Regularity MeasureTheory Filter
open TopologicalSpace (Compacts)
open scoped Topology ENNReal BigOperators Matrix.Norms.Elementwise

private theorem main_metric_pair_admissible
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) :
    ∀ i : Fin 2, IsAdmissibleMetric (![g1, g2] i) := by
  intro i
  fin_cases i
  · exact hg1
  · exact hg2

/-- Exact native finite-rank producer for the Main transfer branch. -/
theorem local_harmonic_finite_rank_restriction
    (a : Fin 2 → MatrixField) (ha : ∀ i : Fin 2, IsAdmissibleMetric (a i))
    (B : ℝ) (hB : 0 < B) (r_ext : ℝ) (hr_ext : 0 < r_ext) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧
      lambda0 * B < min r_ext (5 / 4 : ℝ) ∧
      (∀ (i : Fin 2) (m : ℕ) (d : ℝ), 0 < d →
        ∃ J : ℝ, 0 < J ∧
        ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
        ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0 : R3) B →
        let A : MatrixField := principalCoefficient (fun y : R3 => a i (lambda • y))
        let hA : ContDiffOn ℝ ∞ A D :=
          ((contDiff_principalCoefficient (a i) (ha i)).comp
            (contDiff_const_smul lambda)).contDiffOn
        let H := classicalHarmonicL2Space D hD A hA
        ∀ K : Compacts R3, (∀ x ∈ (K : Set R3), closedBall x d ⊆ D) →
        letI : CompactSpace K := TopologicalSpace.Compacts.instCompactSpaceSubtypeMem K
        letI : SeminormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMultilinearMap.normedSpace (𝕜 := ℝ) (𝕜' := ℝ)
            (E := fun _ : Fin m => R3) (G := ℝ)
        letI : SeminormedAddCommGroup C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) :=
          ContinuousMap.instSeminormedAddCommGroup
        letI : NormedSpace ℝ C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ) := ContinuousMap.normedSpace
        letI : NormedSpace ℝ H := ClosedSubmodule.normedSpace H
        ∃ E : H →L[ℝ] C(K, ContinuousMultilinearMap ℝ (fun _ : Fin m => R3) ℝ),
          ‖E‖ ≤ J ∧
          ∀ (w : H) (f : R3 → ℝ), ContDiffOn ℝ ∞ f D →
            (∀ x ∈ D, divCoeffGrad A f x = 0) →
            ∀ hf : MemLp f 2 ((volume : Measure R3).restrict D),
              hf.toLp f = (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) →
              ∀ x : K, E w x = iteratedFDeriv ℝ m f (x : R3)) ∧
      ∀ (i : Fin 2) (k : ℕ), 1 ≤ k → ∀ d : ℝ, 0 < d →
      ∃ JH : Fin (k + 1) → ℝ, (∀ j : Fin (k + 1), 0 < JH j) ∧
      ∃ CT : ℝ, 0 < CT ∧
      let J_k : ℝ := max (JH ⟨k, Nat.lt_succ_self k⟩) ((Nat.factorial k : ℝ) * CT)
      let n0 : ℕ := 1 + Nat.ceil (2 * Real.sqrt 3 / d)
      let G_B : ℕ := Nat.ceil ((2 * B + 4) ^ 3)
      let M_k : ℕ := ∑ j ∈ Finset.range k, 3 ^ j
      let V_B : ℝ := ((volume : Measure R3) (ball (0 : R3) B)).toReal
      let Q_k : ℝ := Real.sqrt V_B * J_k * (Real.sqrt 3) ^ k / (Nat.factorial k : ℝ)
      let Cerror : ℝ := 1 + max ((n0 : ℝ) ^ k) Q_k
      0 < Cerror ∧
      ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
      ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0 : R3) B →
      let A : MatrixField := principalCoefficient (fun y : R3 => a i (lambda • y))
      let hA : ContDiffOn ℝ ∞ A D :=
        ((contDiff_principalCoefficient (a i) (ha i)).comp
          (contDiff_const_smul lambda)).contDiffOn
      let H := classicalHarmonicL2Space D hD A hA
      ∀ (S : Set R3) (hS : IsOpen S), S.Nonempty → IsCompact (closure S) →
      (∀ x ∈ closure S, closedBall x (2 * d) ⊆ D) →
      ∀ hSD : S ⊆ D,
      let R : H →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S) :=
        (Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
          (show (volume : Measure R3).restrict S ≤
            (1 : ℝ≥0∞) • (volume : Measure R3).restrict D from
            by simpa only [one_smul] using Measure.restrict_mono_set volume hSD)).comp
          H.toSubmodule.subtypeL
      ‖R‖ ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n →
      ∃ T : H →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S),
        FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ G_B * n ^ 3 * M_k ∧
        ‖R - T‖ ≤ Cerror / ((n : ℝ) ^ k) ∧
        (n < n0 → T = 0)  :=
  Regularity.exists_uniform_dilated_metric_harmonic_compact_jets_and_finite_rank_restriction a ha B hB r_ext hr_ext

end FiniteRankRestrictionIntegration

theorem exists_isometryFixingExterior_of_chosen_cover_finite_physical_coercivity (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hLambda : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g1 f = minimalEnergy g2 f)
    (hCoercive : MixedKernelConstructionTask.TwoSidedOriginalChosenCoverFinitePhysicalCoercivity g1 g2) :
    ∃ Phi : R3 ≃ R3, IsIsometryFixingExterior Phi g1 g2 := by
  classical
  let hreg : FixedDirichletRegularity := fixedDirichletRegularity
  let hcalc : FixedSobolevCalculus := fixedSobolevCalculus
  let hSep : RadiusTwoSourceSeparation := radiusTwoSourceSeparation
  have hFiniteRank := local_harmonic_finite_rank_restriction ![g1, g2]
    (main_metric_pair_admissible g1 g2 hg1 hg2)
  have hJointRegularity
      (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
      (i : Fin 2) (L : ℝ) (y0 : R3)
      (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
      (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
      (hData : DriftBootstrap.JointConformalReferenceFramedDriftData
        (![g1,g2] i) L y0 Φ B ε C ρ H a w) :=
    DriftBootstrap.exists_reference_commonRadius_adjointSmoothMultiplier_extended_center_joint_jets
      (T := T) (![g1,g2] i) L y0 Φ B ε C ρ H a w hData
      (main_metric_pair_admissible g1 g2 hg1 hg2 i) hcalc hreg
  have hImage :
      Set.range (fun p : (radiusTwoOpens : Set R3) =>
        radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (p : R3)) =
      Set.range (fun q : (radiusTwoOpens : Set R3) =>
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 (q : R3)) := by
    exact MixedKernelConstructionTask.original_sourceEvaluation_ranges_eq_of_chosen_cover_finite_physical_coercivity
      g1 g2 hg1 hg2 hLambda hCoercive
  let e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3) :=
    radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g2 g1 hg2 hg1 hImage.symm
  let F : R3 → R3 := fun x => if hx : x ∈ (radiusTwoOpens : Set R3) then
    (e ⟨x,hx⟩ : R3) else x
  let G : R3 → R3 := fun x => if hx : x ∈ (radiusTwoOpens : Set R3) then
    (e.symm ⟨x,hx⟩ : R3) else x
  have hF : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      F x = (e ⟨x,hx⟩ : R3) := by
    intro x hx
    simp only [F, dite_eq_left hx]
  have hG : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      G x = (e.symm ⟨x,hx⟩ : R3) := by
    intro x hx
    simp only [G, dite_eq_left hx]
  have hAnn : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e ⟨x,hx⟩ : R3) = x := by
    intro x hx hnorm
    have hxE : x ∈ (exteriorAnnulusOpens : Set R3) :=
      ⟨hnorm, mem_ball_zero_iff.mp hx⟩
    exact congrArg Subtype.val (radiusTwoSourcePartnerHomeomorph_eq_self_of_exterior
      hreg hcalc hSep g2 g1 hg2 hg1 hImage.symm
      (fun f hf => (hLambda f hf).symm) ⟨x,hx⟩ hxE)
  have hSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ F x :=
    contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped
      hreg hcalc hSep g1 g2 hg1 hg2 hImage.symm F hF
  have hInvSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ G x :=
    contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped_symm
      hreg hcalc hSep g1 g2 hg1 hg2 hImage.symm G hG
  let Phi : R3 ≃ R3 := radiusTwoIdentityExtensionEquiv e F G hF hG
  have hPhi : ContDiff ℝ ∞ (Phi : R3 → R3) :=
    contDiff_radiusTwoIdentityExtension e F hF hAnn hSmooth
  have hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3) :=
    contDiff_radiusTwoIdentityExtension e.symm G hG
      (radiusTwoHomeomorph_symm_fixes_annulus e hAnn) hInvSmooth
  have hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x :=
    radiusTwoIdentityExtension_fixes_exterior e F hF hAnn hSmooth
  have hMatch : ∀ x ∈ (radiusTwoOpens : Set R3),
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s x =
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (Phi x) := by
    intro x hx s
    have hPhiAt : Phi x = (e ⟨x,hx⟩ : R3) :=
      (radiusTwoIdentityExtension_apply_of_mem F x hx).trans (hF x hx)
    rw [hPhiAt]
    exact (radiusTwoSourcePartnerHomeomorph_response hreg hcalc hSep
      g2 g1 hg2 hg1 hImage.symm ⟨x,hx⟩ s).symm
  exact ⟨Phi, hPhi, hInv, hFix,
    metric_eq_pullback_of_source_response_eq g1 g2 hg1 hg2 Phi hPhi hInv hFix hMatch⟩

end OAI.AnisotropicCalderon.MainAssemblyWithTransferProducer
#print OAI.AnisotropicCalderon.MainAssemblyWithTransferProducer.exists_isometryFixingExterior_of_chosen_cover_finite_physical_coercivity
#print axioms OAI.AnisotropicCalderon.MainAssemblyWithTransferProducer.exists_isometryFixingExterior_of_chosen_cover_finite_physical_coercivity
