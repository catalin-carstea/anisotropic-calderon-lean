import Calderon.ActualFiniteHarmonicProductRadialSecondRemainder
import Calderon.ActualReferenceWeakRoom

/-! The normalized high graph on finite inputs, derived for the radial remainder of the finite
harmonic product. -/
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

attribute [local irreducible] referenceFiniteHarmonicProductHighRadialFamily
  referenceFiniteHarmonicProductHighSecondRemainder referenceSharpRadialTraceFamily
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  nativeThreeHalfCoefficientMulL sphereSobolevInclusionL

local instance referenceFiniteHarmonicProductRadialRemainderGraphHighCompleteSpace : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFiniteHarmonicProductRadialRemainderGraphHalfCompleteSpace : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFiniteHarmonicProductRadialRemainderGraphHighOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

local instance referenceFiniteHarmonicProductRadialRemainderGraphHighToHalfOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

theorem exists_reference_commonRadius_finiteProductHighSecondRemainder_graph
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ δ →
        ∀ (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (referenceFiniteHarmonicProductHighSecondRemainder
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q q y r f) =
          secondTaylorRemainder (fun t : ℝ => referenceSharpRadialTraceFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
              (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
                (sphereSobolevPartialSum (3/2 : ℝ) n f)) := by
  obtain ⟨lam,Lam,d0,_,hd0,hd0ρ,hUE,hSmall⟩ :=
    exists_reference_commonRadius_weakDriftData g L y0 Φ B ε C ρ H a w hData
  refine ⟨d0/2,by positivity,(by linarith),?_⟩
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
  let A : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun t =>
    referenceFiniteHarmonicProductHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q (q,(y,t))
  let S : ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun t =>
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
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
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) :=
    (contDiffAt_referenceFiniteHarmonicProductHighRadialFamily_fixed
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q (q,(y,θ*r))
        (hHigh (θ*r) (hScaled θ hθ).le)).comp
          (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hSS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ S (θ*r) :=
    (contDiffAt_referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,θ*r))
        (hLow (θ*r) (hScaled θ hθ).le)).comp
          (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => Post (A t)) =ᶠ[𝓝 (θ*r)] (fun t => Eval (S t)) := by
    have hOpen : IsOpen {t : ℝ | |t| < d0} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hOpen.mem_nhds (hScaled θ hθ)] with t ht
    exact sphereSobolevInclusionL_referenceFiniteHarmonicProductHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel n Q (q,(y,t))
        lam Lam (hUEt t ht.le) (hSmallt t ht.le).1 (hWeak t ht.le) f
  have hSame : Post (secondTaylorRemainder A r) = Eval (secondTaylorRemainder S r) :=
    (secondTaylorRemainder_fixed_linear_map A Post r hAS).trans
      ((secondTaylorRemainder_eq_of_locallyEq_on_segment
        (fun t => Post (A t)) (fun t => Eval (S t)) r hEq).trans
          (secondTaylorRemainder_fixed_linear_map S Eval r hSS).symm)
  simpa only [referenceFiniteHarmonicProductHighSecondRemainder,Post,Eval,A,S,I,v,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply] using hSame

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteProductHighSecondRemainder_graph
