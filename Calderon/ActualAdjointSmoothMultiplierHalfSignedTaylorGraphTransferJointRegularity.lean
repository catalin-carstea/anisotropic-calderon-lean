import Calderon.ActualAdjointHighSmoothMultiplierSignedTaylorGraphTransferJointRegularity
import Calderon.ActualAdjointRadialSmoothMultiplierSignedTaylorFactor
import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.SphereSobolevBalancedDualEndpointExtension
import Calderon.SphereSobolevBesselOrderCompatibility
import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.SphereSobolevTangentialEndpointCompatibility

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

local instance adjointMultiplierHalfGraphHiComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance adjointMultiplierHalfGraphHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance adjointMultiplierHalfGraphNegComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily secondTaylorRemainder nativeThreeHalfCoefficientMulL
  nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL sphereSobolevInclusionL
  realHalfOperatorAdjointL

theorem exists_reference_commonRadius_adjointSmoothMultiplierHalfSecondRemainder_graph
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (hg : IsAdmissibleMetric g) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
      ∀ (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
        (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ p x, x ∉ Km → m (p,x)=0)
        (pcoef : ℝ × (R3 × ℝ)),
      let Q := commonSupportCoefficientFamily 3 m hm Km hKm hmz pcoef
      let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      let Gh := secondTaylorRemainder (fun t : ℝ =>
        referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,t))) r
      let GS := secondTaylorRemainder (fun t : ℝ =>
        referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r
      let Gn := -realHalfOperatorAdjointL GS
      ∃ G : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ),
        (∀ u, G (I u) = I (Gh u)) ∧ (∀ v, J (G v) = Gn (J v)) ∧
          ‖G‖ ≤ (‖Gh‖+‖Gn‖)/2 := by
  have hHighRadius := exists_reference_commonRadius_adjointHighSmoothMultiplierSecondRemainder_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel hg
  rcases hHighRadius with ⟨dh,hdh,hdhρ,hHigh⟩
  have hRoomRadius := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases hRoomRadius with ⟨lam,Lam,dw,hlam,hdw,hdwρ,hRoom⟩
  refine ⟨min dh (dw/2),lt_min hdh (half_pos hdw),(min_le_left _ _).trans hdhρ,?_⟩
  intro q hq y hy r hr m hm Km hKm hmz pcoef Q I J Gh GS Gn
  have hrh : |r| ≤ dh := hr.trans (min_le_left _ _)
  have hrw : |r| ≤ dw := (hr.trans (min_le_right _ _)).trans (by linarith only [hdw])
  have hyBall : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    intro θ hθ
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hθr : |θ*r| ≤ dw := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans (by simpa only [one_mul] using hrw)
    exact (hRoom (q,(y,θ*r)) ⟨hq,hyBall,abs_le.mp hθr⟩).2.2.1
  let Hi := SphereSobolev (3/2 : ℝ)
  let Half := SphereSobolev (1/2 : ℝ)
  let Neg := SphereSobolev (-(1/2 : ℝ))
  let Low := SphereSobolev (-(3/2 : ℝ))
  let K : Hi →L[ℝ] Neg := sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Th := secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
  let Tl := secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
  let Mh := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let Ml := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let Mn := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  have hK (u : Hi) : K u = J (I u) := by
    exact (congrArg (fun A : Hi →L[ℝ] Neg => A u)
      (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (by norm_num))).symm
  have hMh (u : Hi) : I (Mh u) = Ml (I u) := by
    have h := nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
      Q (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm
    exact congrArg (fun A : Hi →L[ℝ] Half => A u) h
  have hMl (u : Half) : J (Ml u) = Mn (J u) :=
    congrArg (fun A : Half →L[ℝ] Neg => A u)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q))
  have hT (u : Hi) : J (Th u) = Tl (I u) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A u)
      (referenceAdjointRadialSecondRemainder_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment)
  have hGhigh (u : Hi) : I (Gh u) = Th (Mh u)-Ml (Th u) := hHigh q hq y hy r hrh Q u
  have hNegative := referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0 hKernel q y r pcoef hSegment
  have hGneg (v : Half) : Tl (Ml v)-Mn (Tl v) = Gn (J v) := by
    simpa only [Q,Tl,Ml,Mn,GS,Gn,ContinuousLinearMap.neg_apply] using hNegative.1 v
  have hCompat (u : Hi) : K (Gh u) = Gn (K u) := by
    calc
      K (Gh u) = J (I (Gh u)) := hK (Gh u)
      _ = J (Th (Mh u)-Ml (Th u)) := congrArg J (hGhigh u)
      _ = J (Th (Mh u))-J (Ml (Th u)) := J.map_sub _ _
      _ = Tl (I (Mh u))-Mn (J (Th u)) :=
        congrArg₂ (fun a b : Neg => a-b) (hT (Mh u)) (hMl (Th u))
      _ = Tl (Ml (I u))-Mn (Tl (I u)) :=
        congrArg₂ (fun a b : Neg => a-b) (congrArg Tl (hMh u)) (congrArg Mn (hT u))
      _ = Gn (J (I u)) := hGneg (I u)
      _ = Gn (K u) := congrArg Gn (hK u).symm
  let Bh : Hi →L[ℝ] Half := sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)
  let Bm : Half →L[ℝ] Neg := sphereSobolevBesselOrderL (1/2 : ℝ) (-(1/2 : ℝ))
  let Bn : Neg →L[ℝ] Low := sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))
  let Bi : Neg →L[ℝ] Half := sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)
  let IL : Half →L[ℝ] Low := sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)
  let NL : Neg →L[ℝ] Low := sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
  have hBouter (u : Hi) : IL (Bh u) = Bn (K u) :=
    congrArg (fun A : Hi →L[ℝ] Low => A u)
      (sphereSobolevBesselOrderL_inclusion_comp (3/2 : ℝ) (-(1/2 : ℝ)) (1/2 : ℝ) (-(3/2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hBupper (u : Hi) : J (Bh u) = Bm (I u) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A u)
      (sphereSobolevBesselOrderL_inclusion_comp (3/2 : ℝ) (1/2 : ℝ) (1/2 : ℝ) (-(1/2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hBlower (v : Half) : NL (Bm v) = Bn (J v) :=
    congrArg (fun A : Half →L[ℝ] Low => A v)
      (sphereSobolevBesselOrderL_inclusion_comp (1/2 : ℝ) (-(1/2 : ℝ)) (-(1/2 : ℝ)) (-(3/2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  let H0 := Bh.comp Gh
  let L0 := Bn.comp Gn
  have hc : IL.comp H0 = L0.comp K := by
    apply ContinuousLinearMap.ext
    intro u
    change IL (Bh (Gh u)) = Bn (Gn (K u))
    exact (hBouter (Gh u)).trans (congrArg Bn (hCompat u))
  let M : Half →L[ℝ] Neg := sphereSobolevBalancedDualEndpointL L0 H0 hc
  let G : Half →L[ℝ] Half := Bi.comp M
  have hMupper (u : Hi) : M (I u) = J (Bh (Gh u)) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A u)
      (sphereSobolevBalancedDualEndpointL_upper_inclusion L0 H0 hc)
  have hMlower (v : Half) : NL (M v) = Bn (Gn (J v)) :=
    congrArg (fun A : Half →L[ℝ] Low => A v)
      (sphereSobolevBalancedDualEndpointL_lower_inclusion L0 H0 hc)
  have hBiBm (v : Half) : Bi (Bm v) = v :=
    congrArg (fun A : Half →L[ℝ] Half => A v)
      (sphereSobolevBesselOrderL_inverse (1/2 : ℝ) (-(1/2 : ℝ)))
  have hBmBi (v : Neg) : Bm (Bi v) = v :=
    congrArg (fun A : Neg →L[ℝ] Neg => A v)
      (sphereSobolevBesselOrderL_inverse (-(1/2 : ℝ)) (1/2 : ℝ))
  refine ⟨G,?_,?_,?_⟩
  · intro u
    change Bi (M (I u)) = I (Gh u)
    exact (congrArg Bi (hMupper u)).trans
      ((congrArg Bi (hBupper (Gh u))).trans (hBiBm (I (Gh u))))
  · intro v
    have hEqual : Bn (J (G v)) = Bn (Gn (J v)) :=
      (hBlower (G v)).symm.trans ((congrArg NL (hBmBi (M v))).trans (hMlower v))
    let Bni : Low →L[ℝ] Neg := sphereSobolevBesselOrderL (-(3/2 : ℝ)) (-(1/2 : ℝ))
    have hBniBn (z : Neg) : Bni (Bn z) = z :=
      congrArg (fun A : Neg →L[ℝ] Neg => A z)
        (sphereSobolevBesselOrderL_inverse (-(1/2 : ℝ)) (-(3/2 : ℝ)))
    exact (hBniBn (J (G v))).symm.trans
      ((congrArg Bni hEqual).trans (hBniBn (Gn (J v))))
  · have hGnorm : ‖G‖ ≤ ‖M‖ := by
      exact (Bi.opNorm_comp_le M).trans
        ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _) (norm_nonneg M)).trans_eq (one_mul _))
    have hHnorm : ‖H0‖ ≤ ‖Gh‖ := by
      exact (Bh.opNorm_comp_le Gh).trans
        ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _) (norm_nonneg Gh)).trans_eq (one_mul _))
    have hLnorm : ‖L0‖ ≤ ‖Gn‖ := by
      exact (Bn.opNorm_comp_le Gn).trans
        ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _) (norm_nonneg Gn)).trans_eq (one_mul _))
    exact hGnorm.trans ((norm_sphereSobolevBalancedDualEndpointL_le L0 H0 hc).trans (by linarith only [hHnorm,hLnorm]))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_adjointSmoothMultiplierHalfSecondRemainder_graph
