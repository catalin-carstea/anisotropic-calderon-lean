import Calderon.ActualHalfGaugePoissonReproduction
import Calderon.ParametrixFixedCutoffs
import Calderon.ParameterHadamardDivision
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap
  NativePolynomialBulkMoments SphereHarmonic NativeH2ThreeHalfValueTrace

attribute [local irreducible] referencePhysicalHalfGaugeConormalDensity
  referencePhysicalHalfGaugeCollarHighCorrection referencePhysicalHalfGaugeCollarCorrection
  referencePhysicalHalfGaugeCollarForcing referencePhysicalGaugeCoefficientJets
  ordinaryPrincipalL sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevSingleL parameterHadamardDivision

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referencePhysicalPoissonDensity (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2 : ℝ) :=
  referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc unitBallSmoothCutoff parametrixCollarFactor unitBallSmoothCutoff.contDiff contDiff_parametrixCollarFactor unitBallSmoothCutoff.hasCompactSupport (1/4) (by norm_num) parametrixCollarFactor_zero_of_mem_ball parametrixBoundaryCutoff contDiff_parametrixBoundaryCutoff hF hO hD τ0 p

include hg hData hcalc in
theorem contDiff_referencePhysicalPoissonDensity (hreg : FixedDirichletRegularity) :
    ContDiff ℝ ∞ (referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  exact contDiff_referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc unitBallSmoothCutoff parametrixCollarFactor unitBallSmoothCutoff.contDiff contDiff_parametrixCollarFactor unitBallSmoothCutoff.hasCompactSupport (1/4) (by norm_num) parametrixCollarFactor_zero_of_mem_ball parametrixBoundaryCutoff contDiff_parametrixBoundaryCutoff hF hO hD τ0 hreg

include hg hData hcalc in
theorem exists_compact_uniform_referencePhysicalPoissonDensity_bound
    (hreg : FixedDirichletRegularity) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ p ∈ K, ‖referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ ≤ C0 := by
  exact exists_compact_uniform_referencePhysicalHalfGaugeConormalDensity_bound g hg L y0 Φ B ε C ρ H a w hData hcalc unitBallSmoothCutoff parametrixCollarFactor unitBallSmoothCutoff.contDiff contDiff_parametrixCollarFactor unitBallSmoothCutoff.hasCompactSupport (1/4) (by norm_num) parametrixCollarFactor_zero_of_mem_ball parametrixBoundaryCutoff contDiff_parametrixBoundaryCutoff hF hO hD τ0 hreg K hK

include hg hData hcalc in
theorem referencePhysicalPoissonDensity_reproduces_native_harmonic_smooth
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (u : SmoothData)
    (hP : ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) (smoothBallSobolev 2 u) = 0) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)))),
      τ0.valueTraceL (smoothSobolev u)⟫_ℝ = u.1 0 := by
  exact referencePhysicalHalfGaugeConormalDensity_reproduces_native_harmonic_smooth g hg L y0 Φ B ε C ρ H a w hData hcalc unitBallSmoothCutoff parametrixCollarFactor unitBallSmoothCutoff.contDiff contDiff_parametrixCollarFactor unitBallSmoothCutoff.hasCompactSupport (1/4) (by norm_num) parametrixCollarFactor_zero_of_mem_ball parametrixBoundaryCutoff contDiff_parametrixBoundaryCutoff hreg
    (fun z hz => unitBallSmoothCutoff_one_of_mem hz)
    parametrixCollarFactor_one_of_notMem_closedBall
    parametrixBoundaryCutoff_zero_of_mem_closedBall
    (fun x => parametrixBoundaryCutoff_one_of_mem_sphere x.val x.property)
    hF hO hD τ0 q hq y hy r hr u hP

include hg hData hcalc in
theorem referencePhysicalPoissonDensity_radius_zero_eq_one
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) :
    referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) = sphereSobolevSingleL (3/2 : ℝ) 0 ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩ := by
  exact referencePhysicalHalfGaugeConormalDensity_radius_zero_eq_one g hg L y0 Φ B ε C ρ H a w hData hcalc unitBallSmoothCutoff parametrixCollarFactor unitBallSmoothCutoff.contDiff contDiff_parametrixCollarFactor unitBallSmoothCutoff.hasCompactSupport (1/4) (by norm_num) parametrixCollarFactor_zero_of_mem_ball parametrixBoundaryCutoff contDiff_parametrixBoundaryCutoff hreg
    (fun z hz => unitBallSmoothCutoff_one_of_mem hz)
    parametrixCollarFactor_one_of_notMem_closedBall
    parametrixBoundaryCutoff_zero_of_mem_closedBall
    (fun x => parametrixBoundaryCutoff_one_of_mem_sphere x.val x.property)
    hF hO hD τ0 q hq y hy

def referencePhysicalPoissonRadialDivision (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2 : ℝ) :=
  parameterHadamardDivision (fun x : (ℝ × R3) × ℝ => referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (x.1.1,(x.1.2,x.2)))
    ((p.1,p.2.1),p.2.2)

include hg hData hcalc in
theorem contDiff_referencePhysicalPoissonRadialDivision (hreg : FixedDirichletRegularity) :
    ContDiff ℝ ∞ (referencePhysicalPoissonRadialDivision g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hPi : ContDiff ℝ ∞ (referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := contDiff_referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hF' : ContDiff ℝ ∞ (fun x : (ℝ × R3) × ℝ => referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (x.1.1,(x.1.2,x.2))) :=
    hPi.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  exact (contDiff_parameterHadamardDivision _ hF').comp
    ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)

include hg hData hcalc in
theorem referencePhysicalPoissonDensity_sub_one_eq_radius_smul
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) (r : ℝ) :
    referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) - (sphereSobolevSingleL (3/2 : ℝ) 0 ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩) =
      r • (referencePhysicalPoissonRadialDivision g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) := by
  have hPi : ContDiff ℝ ∞ (referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := contDiff_referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hF' : ContDiff ℝ ∞ (fun x : (ℝ × R3) × ℝ => referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (x.1.1,(x.1.2,x.2))) :=
    hPi.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have h := radius_smul_parameterHadamardDivision _ hF' (q,y) r
  change r • (referencePhysicalPoissonRadialDivision g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) = referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) - referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) at h
  rw [referencePhysicalPoissonDensity_radius_zero_eq_one g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy] at h
  exact h.symm

include hg hData hcalc in
theorem exists_compact_linear_referencePhysicalPoissonDensity_sub_one_bound
    (hreg : FixedDirichletRegularity) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ (q : ℝ), q ∈ Icc (0 : ℝ) 1 → ∀ (y : R3), ‖y-y0‖ ≤ 4*ρ →
      ∀ (r : ℝ), (q,(y,r)) ∈ K →
      ‖referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) - (sphereSobolevSingleL (3/2 : ℝ) 0 ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩)‖ ≤ C0 * |r| := by
  obtain ⟨C0,hC0⟩ := hK.exists_bound_of_continuousOn
    (contDiff_referencePhysicalPoissonRadialDivision g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).continuous.continuousOn
  refine ⟨max C0 1,le_max_right _ _,?_⟩
  intro q hq y hy r hp
  rw [referencePhysicalPoissonDensity_sub_one_eq_radius_smul g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy r,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |r| * max C0 1 := mul_le_mul_of_nonneg_left ((hC0 _ hp).trans (le_max_left _ _)) (abs_nonneg r)
    _ = _ := mul_comm _ _

end OAI.AnisotropicCalderon.ConnectionError
