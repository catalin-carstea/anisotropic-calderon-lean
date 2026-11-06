import Calderon.ActualReferenceGaugeNormalHighCommutator
import Calderon.ActualReferenceGaugeNormalHalfRemainder
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.SignedTaylorFixedLinearTransport
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.ActualReferenceNormalizedSkewDefect
import Calderon.CompactInverseDerivativeBounds

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local instance instCompleteSpaceNormalizedHighDefectHighCarrier :
    CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance instCompleteSpaceNormalizedHighDefectHalfCarrier :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance instCompleteSpaceNormalizedHighDefectHighEnd : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

local instance instCompleteSpaceNormalizedHighDefectHalfEnd : CompleteSpace
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

local instance instCompleteSpaceNormalizedHighDefectHighHalf : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

def referenceNormalizedAdjointHighNormalSecondRemainder (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  secondTaylorRemainder (fun t : ℝ => referenceGaugeNormalHighCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t))) r

attribute [local irreducible] referenceGaugeNormalHighCommutatorFamily
  referenceGaugeNormalHalfCommutatorFamily
  referenceNormalizedAdjointHighNormalSecondRemainder
  referenceGaugeNormalHalfSecondRemainder
  referenceGaugeNormalHighInvertibleLocus
  referenceRadialEndpointInvertibleLocus
  referenceStrongDriftFamily
  referenceWeakDirichletEnergyFamily

lemma contDiffAt_referenceNormalizedAdjointHighNormalSecondRemainder_of_segment
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (R3 × ℝ) => referenceNormalizedAdjointHighNormalSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2) (q,(y,r)) := by
  let curve : (ℝ × R3) × ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun p =>
    referenceGaugeNormalHighCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (p.1.1,(p.1.2,p.2))
  let Ω : Set ((ℝ × R3) × ℝ) := {p | (p.1.1,(p.1.2,p.2)) ∈
    referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc}
  have hΩ : IsOpen Ω := (isOpen_referenceGaugeNormalHighInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hCurve : ContDiffOn ℝ ∞ curve Ω := by
    intro p hp
    have h := contDiffAt_referenceGaugeNormalHighCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (p.1.1,(p.1.2,p.2)) hp
    exact (h.comp (f := fun z : (ℝ × R3) × ℝ => (z.1.1,(z.1.2,z.2))) p
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hTaylor := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    curve Ω hΩ hCurve (q,y) r hSegment
  have hPerm : ContDiffAt ℝ ∞ (fun p : ℝ × (R3 × ℝ) => ((p.1,p.2.1),p.2.2)) (q,(y,r)) :=
    (contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd
  simpa only [referenceNormalizedAdjointHighNormalSecondRemainder,Function.comp_def] using
    hTaylor.comp (f := fun p : ℝ × (R3 × ℝ) => ((p.1,p.2.1),p.2.2)) (q,(y,r)) hPerm

lemma exists_reference_commonRadius_normalizedAdjointHighNormalSecondRemainder_half_agreement
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
          (referenceNormalizedAdjointHighNormalSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r) =
        (referenceGaugeNormalHalfSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r).comp
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  obtain ⟨lam,Lam,d0,_,hd0,hd0ρ,hPhysical⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d0/2,by positivity,(by linarith),?_⟩
  intro q hq y hy r hr
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let highCurve : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun t =>
    referenceGaugeNormalHighCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t))
  let halfCurve : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun t =>
    referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t))
  let Post : (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) →L[ℝ]
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (3/2 : ℝ))
      (SphereSobolev (3/2 : ℝ)) (SphereSobolev (1/2 : ℝ))) I
  let Pre : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →L[ℝ]
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (3/2 : ℝ))
      (SphereSobolev (1/2 : ℝ)) (SphereSobolev (1/2 : ℝ))).flip I
  have hyBall : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| < d0 := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*r| ≤ |r| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)
    linarith
  have hPoint (t : ℝ) (ht : |t| ≤ d0) := hPhysical (q,(y,t)) ⟨hq,hyBall,abs_le.mp ht⟩
  have hHigh (t : ℝ) (ht : |t| ≤ d0) : (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc := by
    unfold referenceGaugeNormalHighInvertibleLocus
    change (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,t)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,t)).IsInvertible
    exact (hPoint t ht).2.2.2.1
  have hHS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ highCurve (θ*r) :=
    (contDiffAt_referenceGaugeNormalHighCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,θ*r))
        (hHigh (θ*r) (hScaled θ hθ).le)).comp
          (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hKS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ halfCurve (θ*r) :=
    (contDiffAt_referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,θ*r))
        (hPoint (θ*r) (hScaled θ hθ).le).2.2.1).comp
          (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => Post (highCurve t)) =ᶠ[𝓝 (θ*r)] (fun t => Pre (halfCurve t)) := by
    have hOpen : IsOpen {t : ℝ | |t| < d0} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hOpen.mem_nhds (hScaled θ hθ)] with t ht
    have hp := hPoint t ht.le
    have hWeak := isInvertible_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t)) lam hp.2.1
    apply ContinuousLinearMap.ext
    intro u
    exact referenceGaugeNormalHighCommutatorFamily_half_agreement
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg (q,(y,t))
        lam Lam hp.1 hp.2.1.1 hWeak u
  have hHighGeneric := secondTaylorRemainder_fixed_linear_map
    (V := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (W := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
  simp (config := { instances := true }) only
    [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hHighGeneric
  have hHighTaylor := hHighGeneric highCurve Post r hHS
  have hHalfGeneric := secondTaylorRemainder_fixed_linear_map
    (V := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (W := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
  simp (config := { instances := true }) only
    [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hHalfGeneric
  have hHalfTaylor := hHalfGeneric halfCurve Pre r hKS
  have hSame := secondTaylorRemainder_eq_of_locallyEq_on_segment
    (fun t => Post (highCurve t)) (fun t => Pre (halfCurve t)) r hEq
  have hOperator : Post (secondTaylorRemainder highCurve r) = Pre (secondTaylorRemainder halfCurve r) :=
    hHighTaylor.trans (hSame.trans hHalfTaylor.symm)
  simpa only [referenceNormalizedAdjointHighNormalSecondRemainder,
    referenceGaugeNormalHalfSecondRemainder,Post,Pre,I,highCurve,halfCurve,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply] using hOperator

variable (Q : Set (ℝ × (R3 × ℝ))) (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)

def referenceNormalizedAdjointHighDefectFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  referenceNormalizedAdjointHighNormalSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 +
    referenceGaugeTangentReciprocalResidualThreeHalfFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p

lemma exists_reference_commonRadius_normalizedAdjointHighDefect_half_agreement
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
          (referenceNormalizedAdjointHighDefectFamily
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r))) =
        (referenceNormalizedAdjointHalfDefectFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r))).comp
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  obtain ⟨d,hd,hdρ,hNormal⟩ :=
    exists_reference_commonRadius_normalizedAdjointHighNormalSecondRemainder_half_agreement
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  refine ⟨d,hd,hdρ,?_⟩
  intro q hq y hy r hr
  have hN := hNormal q hq y hy r hr
  have hB := referenceGaugeTangentReciprocalResidual_high_half_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R (q,(y,r))
  apply ContinuousLinearMap.ext
  intro u
  have hNv := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A u) hN
  have hBv := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A u) hB
  simpa only [referenceNormalizedAdjointHighDefectFamily,referenceNormalizedAdjointHalfDefectFamily,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,map_add] using
      congrArg₂ (fun v w : SphereSobolev (1/2 : ℝ) => v+w) hNv hBv

lemma exists_compact_referenceNormalizedAdjointHighDefectFamily_bounds_of_segment
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K)
    (hSegment : ∀ p ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1,
      (p.1,(p.2.1,θ*p.2.2)) ∈ referenceGaugeNormalHighInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (referenceNormalizedAdjointHighDefectFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) p‖ ≤ M := by
  apply exists_compact_iteratedFDeriv_bound
    (referenceNormalizedAdjointHighDefectFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) K hK
  intro p hp
  have hN := contDiffAt_referenceNormalizedAdjointHighNormalSecondRemainder_of_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 (hSegment p hp)
  have hB := (contDiff_referenceGaugeTangentReciprocalResidualThreeHalfFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R).contDiffAt (x := p)
  exact hN.add hB

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalizedAdjointHighNormalSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceNormalizedAdjointHighNormalSecondRemainder_of_segment
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_normalizedAdjointHighNormalSecondRemainder_half_agreement
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalizedAdjointHighDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_normalizedAdjointHighDefect_half_agreement
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceNormalizedAdjointHighDefectFamily_bounds_of_segment
