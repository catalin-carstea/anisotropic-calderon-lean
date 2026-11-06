import Calderon.ActualReferenceNormalizedHighDefectCompletion
import Calderon.ActualReferenceGaugeTangentHighSkewCompletion
import Calderon.ActualReferenceNormalizedSkewDefect
import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.ActualReferenceAdjointRadialSignedRemainder
import Calderon.ActualReferenceRotationSignedRemainder
import Calderon.ActualReferenceGaugeNormalReciprocalRoom
import Calderon.ActualJacobiHighPhysicalRoomTransferJointRegularity
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Xhigh" => SphereSobolev (3/2 : ℝ)
local notation "Yhalf" => SphereSobolev (1/2 : ℝ)
local notation "Zneg" => SphereSobolev (-(1/2 : ℝ))

local instance actualReferenceHighSkewReciprocalDictionaryCompleteSpaceHalf :
    CompleteSpace Yhalf := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance actualReferenceHighSkewReciprocalDictionaryCompleteSpaceNegativeHalf :
    CompleteSpace Zneg := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceGaugeTangentReciprocalHighSkewFamily
  referenceNormalizedAdjointHighDefectFamily referenceRadialEndpointInvertibleLocus
  referenceLowerRadialTraceSecondRemainder referenceAdjointHalfRadialFamily
  referenceGaugeTangentReciprocalSkewFamily referenceNormalizedAdjointHalfDefectFamily
  secondTaylorRemainder referenceGaugeNormalHighInvertibleLocus
  referenceFramedNormalizedJacobian referenceStrongDriftFamily referenceWeakDirichletEnergyFamily

lemma exists_reference_commonRadius_radialEndpoint_invertible_segment
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
        ∀ r : ℝ, |r| ≤ d → ∀ θ ∈ Icc (0 : ℝ) 1,
          (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
  obtain ⟨d,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_jacobiHighPhysicalRoom
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d,hd,hdρ,?_⟩
  intro q hq y hy r hr θ hθ
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
  have hProduct : |θ*r| ≤ d := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)).trans hr
  exact (hRoom (q,(y,θ*r)) ⟨hq,hyBall,abs_le.mp hProduct⟩).1

lemma referenceAdjointRadialSecondRemainder_sub_eq_highSkew_of_lower_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (R : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hpR : (q,(y,r)) ∈ R.parameterRoom)
    (hAgree : (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
        (referenceNormalizedAdjointHighDefectFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r))) =
      (referenceNormalizedAdjointHalfDefectFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r))).comp
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))) :
            secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r -
              referenceSharpRadialTraceSecondRemainder
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r =
            referenceGaugeTangentReciprocalHighSkewFamily
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
                (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r)) +
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
              (referenceNormalizedAdjointHighDefectFamily
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
                  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r))) := by
  let K0 : Set Pphys := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  let I : Xhigh →L[ℝ] Yhalf := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : Yhalf →L[ℝ] Zneg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Sh : Xhigh →L[ℝ] Yhalf := referenceSharpRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let Th : Xhigh →L[ℝ] Yhalf := secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
  let E : Yhalf →L[ℝ] Zneg := referenceLowerRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let Tl : Yhalf →L[ℝ] Zneg := secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
  let Vh : Xhigh →L[ℝ] Yhalf := referenceGaugeTangentReciprocalHighSkewFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 K0 R (q,(y,r))
  let Vl : Yhalf →L[ℝ] Zneg := referenceGaugeTangentReciprocalSkewFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 K0 R (q,(y,r))
  let Dh : Xhigh →L[ℝ] Xhigh := referenceNormalizedAdjointHighDefectFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 K0 R (q,(y,r))
  let Dl : Yhalf →L[ℝ] Yhalf := referenceNormalizedAdjointHalfDefectFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 K0 R (q,(y,r))
  have hS : J.comp Sh = E.comp I := referenceSharpRadialTraceSecondRemainder_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
  have hT : J.comp Th = Tl.comp I := referenceAdjointRadialSecondRemainder_high_half_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hTranspose : Tl = sphereLowerDistributionalTranspose E := by
    simpa only [Tl,E,referenceLowerRadialTraceSecondRemainder] using
      secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by linarith [hData.1.2.1]
  have hSkew : sphereLowerDistributionalTranspose E-E = Vl+J.comp Dl :=
    referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_skew_add_half
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 K0 R hKernel
        q hq y hy2 r hSegment hpR
  have hV : J.comp Vh = Vl.comp I := referenceGaugeTangentReciprocalHighSkewFamily_lower_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 K0 R (q,(y,r))
  have hDpoint : I.comp Dh = Dl.comp I := hAgree
  change Th-Sh = Vh+I.comp Dh
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hSv : J (Sh u) = E (I u) := congrArg (fun A : Xhigh →L[ℝ] Zneg => A u) hS
  have hTv : J (Th u) = Tl (I u) := congrArg (fun A : Xhigh →L[ℝ] Zneg => A u) hT
  have hVv : J (Vh u) = Vl (I u) := congrArg (fun A : Xhigh →L[ℝ] Zneg => A u) hV
  have hDv : I (Dh u) = Dl (I u) := congrArg (fun A : Xhigh →L[ℝ] Yhalf => A u) hDpoint
  have hKv : sphereLowerDistributionalTranspose E (I u)-E (I u) = Vl (I u)+J (Dl (I u)) := by
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply] using congrArg (fun A : Yhalf →L[ℝ] Zneg => A (I u)) hSkew
  change J (Th u-Sh u) = J (Vh u+I (Dh u))
  calc
    _ = J (Th u)-J (Sh u) := J.map_sub _ _
    _ = Tl (I u)-E (I u) := congrArg₂ (fun v w : Zneg => v-w) hTv hSv
    _ = Vl (I u)+J (Dl (I u)) := by rw [hTranspose]; exact hKv
    _ = J (Vh u)+J (I (Dh u)) :=
      congrArg₂ (fun v w : Zneg => v+w) hVv.symm (congrArg J hDv).symm
    _ = _ := (J.map_add _ _).symm


lemma exists_reference_commonRadius_high_defect_lower_graph_segment
    (hreg : FixedDirichletRegularity)
    (R : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ δ →
        (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧ (q,(y,r)) ∈ R.parameterRoom ∧
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
        (referenceNormalizedAdjointHighDefectFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r))) =
      (referenceNormalizedAdjointHalfDefectFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r))).comp
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let K0 : Set Pphys := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  obtain ⟨dH,hdH,hdHρ,hAgree⟩ :=
    exists_reference_commonRadius_normalizedAdjointHighDefect_half_agreement
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 K0 R hreg
  obtain ⟨dP,hdP,hdPρ,hRoom⟩ := exists_reference_commonRadius_radialEndpoint_invertible_segment
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let δ : ℝ := min (dH/2) (dP/2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδH : δ ≤ dH := by
    have h := min_le_left (dH/2) (dP/2)
    dsimp only [δ]
    linarith
  have hδP : δ ≤ dP := by
    have h := min_le_right (dH/2) (dP/2)
    dsimp only [δ]
    linarith
  have hδρ : δ ≤ ρ := hδH.trans hdHρ
  refine ⟨δ,hδ,hδρ,?_⟩
  intro q hq y hy r hr
  have hyBall : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    exact hRoom q hq y hy r (hr.trans hδP)
  have hpR : (q,(y,r)) ∈ R.parameterRoom :=
    R.containsCompact ⟨hq,hyBall,abs_le.mp (hr.trans hδρ)⟩
  exact ⟨hSegment,hpR,hAgree q hq y hy r (hr.trans hδH)⟩


lemma exists_reference_commonRadius_high_skew_dictionary_of_reciprocalRoom
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (R : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
        ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
          ∀ r : ℝ, |r| ≤ δ →
            secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r -
              referenceSharpRadialTraceSecondRemainder
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r =
            referenceGaugeTangentReciprocalHighSkewFamily
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
                (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r)) +
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
              (referenceNormalizedAdjointHighDefectFamily
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
                  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) R (q,(y,r))) := by
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_high_defect_lower_graph_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg R
  refine ⟨δ,hδ,hδρ,?_⟩
  intro q hq y hy r hr
  have hPoint := hRoom q hq y hy r hr
  exact referenceAdjointRadialSecondRemainder_sub_eq_highSkew_of_lower_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel R
      q hq y hy r hPoint.1 hPoint.2.1 hPoint.2.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_radialEndpoint_invertible_segment
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointRadialSecondRemainder_sub_eq_highSkew_of_lower_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_high_defect_lower_graph_segment
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_high_skew_dictionary_of_reciprocalRoom
