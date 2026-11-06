import Calderon.ActualFiniteGaugeAdjointSecondRemainder
import Calderon.ActualFiniteGaugeAdjointRadialGraph
import Calderon.ActualFiniteGaugeAdjointValueGraphTopology
import Calderon.ActualReferenceWeakRoom
import Calderon.ActualReferenceRadialEndpointOpenLocus

/-! Signed remainder graph for the normalized adjoint finite input, with Q frozen. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

attribute [local irreducible] referenceFiniteGaugeAdjointRadialFamily
  referenceFiniteGaugeAdjointSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  referenceRadialEndpointInvertibleLocus
  nativeThreeHalfCoefficientMulL sphereSobolevInclusionL

local instance referenceFiniteGaugeAdjointRemainderGraphHighCompleteSpace : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFiniteGaugeAdjointRemainderGraphHalfCompleteSpace : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFiniteGaugeAdjointRemainderGraphHighOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

local instance referenceFiniteGaugeAdjointRemainderGraphHighToHalfOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

theorem exists_reference_commonRadius_finiteGaugeAdjointSecondRemainder_graph
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∃ G : ReferenceGaugeNormalReciprocalRoom g L Φ a
        (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-(2*δ)) (2*δ))),
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ δ →
        ∀ (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (referenceFiniteGaugeAdjointSecondRemainder
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q q y r f) =
          secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
              (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
                (sphereSobolevPartialSum (3/2 : ℝ) n f)) := by
  obtain ⟨lam,Lam,d0,_,hd0,hd0ρ,hUE,hSmall⟩ :=
    exists_reference_commonRadius_weakDriftData g L y0 Φ B ε C ρ H a w hData
  refine ⟨d0/2,by positivity,(by linarith),?_⟩
  let Tube : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-(2*(d0/2))) (2*(d0/2)))
  have hTube : IsCompact Tube := isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  let G := referenceGaugeNormalReciprocalRoomOfCompact g L Φ y0 B ε C ρ H a w hData hg Tube hTube
  refine ⟨G,?_⟩
  intro q hq y hy r hr n Q f
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hUEt (t : ℝ) (ht : |t| ≤ d0) :
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun z => a ((q,(y,t)),z)) lam Lam :=
    hUE (q,(y,t)) ⟨hq,hyBall,abs_le.mp (ht.trans hd0ρ)⟩
  have hSmallt (t : ℝ) (ht : |t| ≤ d0) := hSmall q hq y hy t ht
  have hHigh (t : ℝ) (ht : |t| ≤ d0) :
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,t)).IsInvertible :=
    referenceStrongDriftFamily_isInvertible_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg 1 q (y,t) lam Lam (hUEt t ht) (hSmallt t ht).1
  have hLow (t : ℝ) (ht : |t| ≤ d0) :
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,t)).IsInvertible :=
    referenceStrongDriftFamily_isInvertible_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q (y,t) lam Lam (hUEt t ht) (hSmallt t ht).1
  have hWeak (t : ℝ) (ht : |t| ≤ d0) :
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t))).IsInvertible :=
    isInvertible_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t)) lam (hSmallt t ht)
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| < d0 := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*r| ≤ |r| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)
    linarith
  have hEndpoint (t : ℝ) (ht : |t| ≤ d0) :
      (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    referenceRadialEndpointInvertibleLocus_mem_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (q,(y,t)) lam Lam
        (hUEt t ht) (hSmallt t ht)
  have hGRoom (t : ℝ) (ht : |t| ≤ d0) : (q,(y,t)) ∈ G.parameterRoom := by
    apply G.containsCompact
    have ht' : |t| ≤ 2*(d0/2) := by linarith
    exact ⟨hq,hyBall,abs_le.mp ht'⟩
  let A : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun t =>
    referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q (q,(y,t))
  let S : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun t =>
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let v : SphereSobolev (3/2 : ℝ) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
    (sphereSobolevPartialSum (3/2 : ℝ) n f)
  let Post : (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) →L[ℝ]
      SphereSobolev (1/2 : ℝ) :=
    I.comp (ContinuousLinearMap.apply ℝ (SphereSobolev (3/2 : ℝ)) f)
  let Eval : (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →L[ℝ]
      SphereSobolev (1/2 : ℝ) :=
    ContinuousLinearMap.apply ℝ (SphereSobolev (1/2 : ℝ)) v
  let m : (ℝ × (R3 × ℝ)) × R3 → ℝ := fun z => coefficientValue 3 Q z.2
  let KQ : Set R3 := tsupport (coefficientValue 3 Q)
  have hm : ContDiff ℝ ∞ m := (contDiff_coefficientValue 3 Q).comp contDiff_snd
  have hKQ : IsCompact KQ := hasCompactSupport_coefficientValue 3 Q
  have hzQ : ∀ p x, x ∉ KQ → m (p,x)=0 := by
    intro p x hx
    by_contra hn
    exact hx (subset_tsupport (coefficientValue 3 Q) hn)
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) :=
    (contDiffAt_referenceFiniteGaugeAdjointRadialFamily_of_value_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n m hm KQ hKQ hzQ
        (fun _ => Q) (fun _ => rfl) (q,(y,θ*r))
        (hHigh (θ*r) (hScaled θ hθ).le)).comp
          (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hSS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ S (θ*r) := by
    have hPoint := (contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds
            (hEndpoint (θ*r) (hScaled θ hθ).le))
    exact hPoint.comp (f := fun t : ℝ => (q,(y,t))) (θ*r)
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => Post (A t)) =ᶠ[𝓝 (θ*r)] (fun t => Eval (S t)) := by
    have hOpen : IsOpen {t : ℝ | |t| < d0} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hOpen.mem_nhds (hScaled θ hθ)] with t ht
    exact sphereSobolevInclusionL_referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel G n Q q hq y hy
        t lam Lam (hUEt t ht.le) (hSmallt t ht.le).1 (hEndpoint t ht.le) (hGRoom t ht.le) f
  have hSame : Post (secondTaylorRemainder A r) = Eval (secondTaylorRemainder S r) :=
    (secondTaylorRemainder_fixed_linear_map A Post r hAS).trans
      ((secondTaylorRemainder_eq_of_locallyEq_on_segment
        (fun t => Post (A t)) (fun t => Eval (S t)) r hEq).trans
          (secondTaylorRemainder_fixed_linear_map S Eval r hSS).symm)
  simpa only [referenceFiniteGaugeAdjointSecondRemainder,Post,Eval,A,S,I,v,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply] using hSame

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteGaugeAdjointSecondRemainder_graph
