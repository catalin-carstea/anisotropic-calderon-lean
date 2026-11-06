import Calderon.NativePolynomialRadialJets
import Calderon.GuardedHarmonicLift
import Calderon.StrongInverseFamily
import Calderon.CommonSupportHarmonicLiftFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError

section General
variable {X Z Y : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem hasDerivAt_guardedHarmonicLiftFamily_apply_zero_of_harmonic
    (J : Z →L[ℝ] X) (A : ℝ → Z →L[ℝ] Y) (hA : ContDiff ℝ ∞ A)
    (B : ℝ → X →L[ℝ] Y) (hB : ContDiff ℝ ∞ B)
    (B' : X →L[ℝ] Y) (hB' : HasDerivAt B B' 0)
    (hi : (A 0).IsInvertible) (E : X) (hE : B 0 E = 0) :
    HasDerivAt (fun r : ℝ => guardedHarmonicLiftFamily J A B r E)
      (-J ((A 0).inverse (B' E))) 0 := by
  have hInv : ContDiffAt ℝ ∞ (fun r : ℝ => (A r).inverse) 0 :=
    hi.contDiffAt_map_inverse.comp 0 hA.contDiffAt
  have hInvD := (hInv.differentiableAt (by simp)).hasDerivAt
  have hResidual := hB'.clm_apply (hasDerivAt_const (0 : ℝ) E)
  have hCorrection := hInvD.clm_apply hResidual
  simp only [hE,map_zero,add_zero,zero_add] at hCorrection
  have hJ := J.hasFDerivAt.comp_hasDerivAt 0 hCorrection
  have hFormula := (hasDerivAt_const (0 : ℝ) E).sub hJ
  simp only [Function.comp_def,zero_sub] at hFormula
  have hNear : ∀ᶠ r : ℝ in 𝓝 0, (A r).IsInvertible :=
    hA.continuous.continuousAt.eventually hi.eventually_nhds
  apply hFormula.congr_of_eventuallyEq
  filter_upwards [hNear] with r hr
  rw [guardedHarmonicLiftFamily_eq J A B r hr,harmonicLiftL_apply]
  rfl

end General

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceStrongDriftFamily (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ)
    (p : R3 × ℝ) : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).comp
    (strongDirichletSubmodule s).toSubmodule.subtypeL

def referenceHarmonicLiftFamily (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) :
    R3 × ℝ → BallSobolev (s+2) →L[ℝ] BallSobolev (s+2) :=
  guardedHarmonicLiftFamily (strongDirichletSubmodule s).toSubmodule.subtypeL
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q)
    (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q)

theorem referenceHarmonicLiftFamily_eq_commonSupport
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) :
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q =
      let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
      commonSupportHarmonicLiftFamily hcalc s
        (jointFixedParameterSlice a q) h.1
        (jointFixedParameterSlice w q) h.2.1
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  have hA : referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q =
      commonSupportStrongDriftFamily hcalc s
        (jointFixedParameterSlice a q) h.1
        (jointFixedParameterSlice w q) h.2.1
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L := by
    funext p
    exact ordinaryStrongDriftFamily_restriction hcalc s _ h.1 _ h.2.1 _ h.2.2.1
      _ (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p
  unfold referenceHarmonicLiftFamily
  rw [hA]
  rfl

theorem contDiff_referenceOrdinaryStrongDriftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) :
    ContDiff ℝ ∞ (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q) := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  exact contDiff_ordinaryStrongDriftFamily hcalc s _ h.1 _ h.2.1 _ h.2.2.1
    _ (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L

theorem referenceStrongDriftFamily_zero_isInvertible
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)).IsInvertible := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  rcases hData.1 with ⟨_,hρ,_,_,_,_,_,_,_,_,_,_,_,hUE,_⟩
  rcases hUE with ⟨lam,Lam,hUE⟩
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hp : (q,(y,(0 : ℝ))) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ) :=
    ⟨hq,hyBall,⟨by linarith,le_of_lt hρ⟩⟩
  have hUE0 := hUE (q,(y,0)) hp
  have hUEBall : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => jointFixedParameterSlice a q ((y,0),z)) lam Lam := by
    refine ⟨hUE0.1,hUE0.2.1,?_⟩
    intro z hz
    exact hUE0.2.2 (by simpa only [coe_ballOpens] using Metric.ball_subset_closedBall hz)
  have hZero : ordinaryStrongDriftFamily hcalc s _ h.1 _ h.2.1 _ h.2.2.1
      _ (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L (y,0) =
      ordinaryPrincipalL hcalc s
        (commonSupportMatrixFamily (s+2) (jointFixedParameterSlice a q) h.1
          (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 (y,0)) := by
    simp only [ordinaryStrongDriftFamily,ordinaryWeightedDriftL,mul_zero,zero_smul,add_zero]
  unfold referenceStrongDriftFamily referenceOrdinaryStrongDriftFamily
  change ((ordinaryStrongDriftFamily hcalc s _ h.1 _ h.2.1 _ h.2.2.1
    _ (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L (y,0)).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible
  rw [hZero,ordinaryPrincipalL_restriction]
  apply strongDirichletOperator_isInvertible_of_elliptic hcalc hreg s
  rw [coefficientMatrixField_commonSupportMatrixFamily]
  exact hUEBall

theorem hasDerivAt_referenceHarmonicLiftFamily_polynomial_zero
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (p : MvPolynomial (Fin 3) ℝ) (hΔ : AngularPolynomial.laplacian p = 0) :
    HasDerivAt
      (fun r : ℝ => referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
        (polynomialBallSobolev (s+2) p))
      ((strongDirichletSubmodule s).toSubmodule.subtypeL
        ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)).inverse
          (polynomialBallSobolev s (GreenRadialTrace.driftDerivative
            (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)))) 0 := by
  let Bs : ℝ → BallSobolev (s+2) →L[ℝ] BallSobolev s :=
    fun r => referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
  let As : ℝ → StrongDirichletSpace s →L[ℝ] BallSobolev s :=
    fun r => referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
  let B' : BallSobolev (s+2) →L[ℝ] BallSobolev s :=
    -∑ i : Fin 3, (referenceCenterDrift g L q y i) • ordinaryLowerOrderCoordinateDerivativeL hcalc s i
  have hBs : ContDiff ℝ ∞ Bs :=
    (contDiff_referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q).comp
      (contDiff_const.prodMk contDiff_id)
  have hAs : ContDiff ℝ ∞ As := hBs.clm_comp contDiff_const
  have hB' : HasDerivAt Bs B' 0 :=
    hasDerivAt_referenceOrdinaryStrongDriftFamily_zero g L y0 Φ B ε C ρ H a w hData
      hcalc s q hq y hy
  have hi : (As 0).IsInvertible :=
    referenceStrongDriftFamily_zero_isInvertible g L y0 Φ B ε C ρ H a w hData
      hcalc hreg s q hq y hy
  have hE : Bs 0 (polynomialBallSobolev (s+2) p) = 0 := by
    rw [referenceOrdinaryStrongDriftFamily_zero_polynomial g L y0 Φ B ε C ρ H a w hData
      hcalc s q hq y hy,hΔ]
    change -(polynomialBallSobolevLinearMap s 0) = 0
    rw [map_zero,neg_zero]
  have hj := hasDerivAt_guardedHarmonicLiftFamily_apply_zero_of_harmonic
    (Z := StrongDirichletSpace s)
    (strongDirichletSubmodule s).toSubmodule.subtypeL As hAs Bs hBs B' hB' hi
    (polynomialBallSobolev (s+2) p) hE
  have hb : B' (polynomialBallSobolev (s+2) p) =
      -polynomialBallSobolev s (GreenRadialTrace.driftDerivative
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p) := by
    rw [ContinuousLinearMap.neg_apply,nativePolynomial_drift_operator]
  rw [hb,map_neg,map_neg,neg_neg] at hj
  exact hj

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
