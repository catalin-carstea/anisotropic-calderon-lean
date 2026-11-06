import Calderon.ActualFiveHalfMovingNativeTaylor
import Calderon.ActualHorizontalGeometry
import Calderon.RadiusJetGraphFirstDerivativeBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Pjet" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)

private lemma compact_first_jet_cap
    {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : A → V) (K : Set A) (hK : IsCompact K)
    (hF : ∀ p ∈ K, ContDiffAt ℝ ∞ F p) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ p ∈ K, ‖F p‖ ≤ C0 ∧ ‖fderiv ℝ F p‖ ≤ C0 := by
  have hc : ContinuousOn F K := fun p hp => (hF p hp).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (fderiv ℝ F) K :=
    fun p hp => ((hF p hp).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C1,hC1⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨C2,hC2⟩ := hK.exists_bound_of_continuousOn hdc
  refine ⟨max (max C1 C2) 1,le_max_right _ _,?_⟩
  intro p hp
  exact ⟨(hC1 p hp).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hC2 p hp).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) {K : Set Pphys}
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) K)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceFiveHalfAdjointMovingRegularRemainderInRoom
  referenceFiveHalfAdjointRadialSecondRemainder referenceFiveHalfAdjointJacobiBoundaryInRoom
  referenceNativeMovingAdjointParametricCorrection sphereSobolevInclusionL sphereSobolevConstantOne

theorem contDiffAt_referenceFiveHalfAdjointMovingRegularRemainderInRoom_of_segment
    (hreg : FixedDirichletRegularity) (t : Pjet) (i : Fin 3)
    (hSegment : ∀ theta ∈ Icc (0:ℝ) 1, (t.1.1,(t.1.2.1,theta*t.1.2.2)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : Pjet => referenceFiveHalfAdjointMovingRegularRemainderInRoom
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg E z i) t := by
  have hp : t.1 ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    simpa only [one_mul,Prod.eta] using hSegment 1 (by simp)
  have hT := (contDiffAt_referenceFiveHalfAdjointRadialSecondRemainder_of_segment
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg t.1.1 t.1.2.1 t.1.2.2 hSegment).comp t contDiffAt_fst
  have hJ := (contDiffAt_referenceFiveHalfAdjointJacobiBoundaryInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg t.1 i hp).comp t contDiffAt_fst
  have hParam : ContDiff ℝ ∞ (fun z : Pjet => (z.1.1,z.1.2.1)) := by fun_prop
  have hFrame := ((contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp hParam).contDiffAt (x := t)
  have hEll : ContDiffAt ℝ ∞ (fun z : Pjet =>
      z.2 (conformalReferenceGramFrameOperatorJoint g L (z.1.1,z.1.2.1) (coordinateVector i))) t :=
    contDiffAt_snd.clm_apply (hFrame.clm_apply contDiffAt_const)
  unfold referenceFiveHalfAdjointMovingRegularRemainderInRoom
  exact ((hT.clm_comp contDiffAt_const).add hJ).add (hEll.smul hT)

def referenceFiveHalfConstantFirstRegularPartInRoom (t : Pjet) (i : Fin 3) : SphereSobolev (3/2:ℝ) :=
  sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
    (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (5/2:ℝ)
      ((t.1.1,t.1.2.1),t.2) i (sphereSobolevConstantOne (5/2:ℝ))) +
  t.1.2.2 • referenceFiveHalfAdjointMovingRegularRemainderInRoom
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg E t i (sphereSobolevConstantOne (5/2:ℝ))

theorem contDiffAt_referenceFiveHalfConstantFirstRegularPartInRoom_of_segment
    (hreg : FixedDirichletRegularity) (t : Pjet) (i : Fin 3)
    (hSegment : ∀ theta ∈ Icc (0:ℝ) 1, (t.1.1,(t.1.2.1,theta*t.1.2.2)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : Pjet => referenceFiveHalfConstantFirstRegularPartInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 z i) t := by
  have hParam : ContDiff ℝ ∞ (fun z : Pjet => ((z.1.1,z.1.2.1),z.2)) := by fun_prop
  have hCorr : ContDiffAt ℝ ∞ (fun z : Pjet =>
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L (5/2:ℝ)
        ((z.1.1,z.1.2.1),z.2) i (sphereSobolevConstantOne (5/2:ℝ))) t :=
    (((contDiff_referenceNativeMovingAdjointParametricCorrection hF hO hD
      g hg L (5/2:ℝ) i).comp hParam).contDiffAt (x := t)).clm_apply contDiffAt_const
  have hFirst : ContDiffAt ℝ ∞ (fun z : Pjet =>
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (5/2:ℝ)
          ((z.1.1,z.1.2.1),z.2) i (sphereSobolevConstantOne (5/2:ℝ)))) t :=
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.contDiffAt.comp t hCorr
  have hRem : ContDiffAt ℝ ∞ (fun z : Pjet =>
      referenceFiveHalfAdjointMovingRegularRemainderInRoom
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg E z i (sphereSobolevConstantOne (5/2:ℝ))) t :=
    (contDiffAt_referenceFiveHalfAdjointMovingRegularRemainderInRoom_of_segment
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg t i hSegment).clm_apply contDiffAt_const
  unfold referenceFiveHalfConstantFirstRegularPartInRoom
  exact hFirst.add (contDiffAt_fst.snd.snd.smul hRem)

theorem exists_uniform_referenceFiveHalfConstantFirstRegularPartInRoom_joint_first_jets
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∃ M : ℝ, 1 ≤ M ∧
      ∀ q ∈ Icc (0:ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
      ∀ r : ℝ, |r| ≤ d → ∀ ell : R3 →L[ℝ] ℝ, ‖ell‖ ≤ 1 → ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (fun t : Pjet => referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 t i) ((q,(y,r)),ell) ∧
      ‖referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(y,r)),ell) i‖ ≤ M ∧
      ‖fderiv ℝ (fun t : Pjet => referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 t i) ((q,(y,r)),ell)‖ ≤ M := by
  obtain ⟨d0,hd0,hd0ρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let d := min d0 1
  let J : Set Pjet := (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ×ˢ
    closedBall (0 : R3 →L[ℝ] ℝ) 1
  have hJ : IsCompact J :=
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)).prod (isCompact_closedBall _ _)
  let F (i : Fin 3) (t : Pjet) := referenceFiveHalfConstantFirstRegularPartInRoom
    g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 t i
  have hSmooth (i : Fin 3) (t : Pjet) (ht : t ∈ J) : ContDiffAt ℝ ∞ (F i) t := by
    apply contDiffAt_referenceFiveHalfConstantFirstRegularPartInRoom_of_segment
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg
    intro theta htheta
    have hr : |t.1.2.2| ≤ d0 := (abs_le.mpr ht.1.2.2).trans (min_le_left _ _)
    have htr : |theta*t.1.2.2| ≤ d0 := by
      rw [abs_mul,abs_of_nonneg htheta.1]
      calc theta*|t.1.2.2| ≤ 1*|t.1.2.2| := mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)
           _ ≤ d0 := by simpa only [one_mul] using hr
    exact hRoom ⟨ht.1.1,ht.1.2.1,abs_le.mp htr⟩
  have hCaps (i : Fin 3) := compact_first_jet_cap (F i) J hJ (hSmooth i)
  choose M hM hBound using hCaps
  obtain ⟨C0,hC0⟩ := (Set.finite_range M).bddAbove
  refine ⟨d,lt_min hd0 one_pos,(min_le_left _ _).trans hd0ρ,min_le_right _ _,max C0 1,le_max_right _ _,?_⟩
  intro q hq y hy r hr ell hell i
  have ht : ((q,(y,r)),ell) ∈ J := by
    refine ⟨⟨hq,?_,abs_le.mp hr⟩,?_⟩
    · simpa only [mem_closedBall,dist_eq_norm] using hy
    · simpa only [mem_closedBall,dist_zero_right] using hell
  have hMi : M i ≤ max C0 1 := (hC0 ⟨i,rfl⟩).trans (le_max_left _ _)
  exact ⟨hSmooth i _ ht,((hBound i _ ht).1).trans hMi,((hBound i _ ht).2).trans hMi⟩

theorem exists_uniform_referenceFiveHalfConstantFirstRegularPartInRoom_radius_first_jets
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∃ M : ℝ, 1 ≤ M ∧
      ∀ q ∈ Icc (0:ℝ) 1, ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ y : R3, ‖y-y0‖ ≤ ρ → |R y| ≤ d → ‖fderiv ℝ R y‖ ≤ 1 →
      ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ 1 → ∀ i : Fin 3,
      ‖referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(y,R y)),fderiv ℝ R y) i‖ ≤ M ∧
      ‖fderiv ℝ (fun z => referenceFiveHalfConstantFirstRegularPartInRoom
        g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 ((q,(z,R z)),fderiv ℝ R z) i) y‖ ≤ M := by
  obtain ⟨d,hd,hdρ,hd1,M,hM,hBound⟩ :=
    exists_uniform_referenceFiveHalfConstantFirstRegularPartInRoom_joint_first_jets
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 hreg
  refine ⟨d,hd,hdρ,hd1,M,hM,?_⟩
  intro q hq R hR y hy hr hDR hD2R i
  have h := hBound q hq y hy (R y) hr (fderiv ℝ R y) hDR i
  refine ⟨h.2.1,?_⟩
  exact norm_fderiv_radiusJetGraph_pullback_le
    (fun t : Pjet => referenceFiveHalfConstantFirstRegularPartInRoom
      g L y0 Φ B ε C ρ H a w hData hg E hcalc hF hO hD τ0 t i) q R y M
    (h.1.differentiableAt (by simp)) (hR.differentiable (by simp) y)
    ((hR.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y) h.2.2 hDR hD2R

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
