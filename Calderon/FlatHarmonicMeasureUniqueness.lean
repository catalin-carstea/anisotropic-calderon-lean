import Calderon.NativeHighDensityTracePairingDictionary
import Calderon.NativePolynomialAnalyticLaplacian
import Calderon.SpherePositiveDensity
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  SphereHilbertDecomposition NativeH2ThreeHalfValueTrace

theorem valueTrace_smoothPolynomialData_eq_polynomialSphereL2
    (τ0 : UnitBallValueTrace) (p : MvPolynomial (Fin 3) ℝ) :
    τ0.valueTraceL (smoothSobolev (smoothPolynomialData p)) = polynomialSphereL2 p := by
  rw [τ0.valueTrace_smooth]
  rfl

theorem sphereL2_eq_one_of_harmonicPolynomial_reproduces
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (w : SphereL2)
    (hRep : ∀ p : MvPolynomial (Fin 3) ℝ, AngularPolynomial.laplacian p = 0 →
      ⟪w, τ0.valueTraceL (smoothSobolev (smoothPolynomialData p))⟫_ℝ =
        (smoothPolynomialData p).1 0) :
    w = polynomialSphereL2 (C 1) := by
  have hPos : w ∈ positiveHarmonicSpanᗮ := by
    apply (positiveHarmonicSpan.mem_orthogonal' w).mpr
    have hle : positiveHarmonicSpan ≤ (ℝ ∙ w)ᗮ := by
      apply iSup_le
      intro k
      rintro v ⟨p,hp,rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      have h := hRep p hp.2
      rw [valueTrace_smoothPolynomialData_eq_polynomialSphereL2] at h
      have hZero : (smoothPolynomialData p).1 0 = 0 := by
        change eval (fun _ => (0 : ℝ)) p = 0
        rw [eval_zero']
        exact hp.1.coeff_eq_zero (by simp)
      exact h.trans hZero
    intro v hv
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hv)
  have hConst : w ∈ sphereConstantSpan := by
    rwa [positiveHarmonic_orthogonal_eq_constants hO hD] at hPos
  rcases Submodule.mem_span_singleton.mp hConst with ⟨c,hc⟩
  have hMass := hRep (C 1) (C_harmonicHomogeneous 1).2
  rw [valueTrace_smoothPolynomialData_eq_polynomialSphereL2,← hc,real_inner_smul_left,
    sphereConstant_inner_self] at hMass
  have hcOne : c = 1 := by simpa [smoothPolynomialData] using hMass
  rw [← hc,hcOne,one_smul]

theorem sphereSobolev_eq_one_of_harmonicPolynomial_reproduces
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (rho : SphereSobolev (3/2 : ℝ))
    (hRep : ∀ p : MvPolynomial (Fin 3) ℝ, AngularPolynomial.laplacian p = 0 →
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) rho),
        τ0.valueTraceL (smoothSobolev (smoothPolynomialData p))⟫_ℝ =
          (smoothPolynomialData p).1 0) :
    rho = sphereSobolevSingleL (3/2 : ℝ) 0
      ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩ := by
  let w : SphereL2 := (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) rho)
  let e : harmonicSphereSubspace 0 :=
    ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩
  have hw : w = polynomialSphereL2 (C 1) :=
    sphereL2_eq_one_of_harmonicPolynomial_reproduces hO hD τ0 w hRep
  have hE : sphereSobolevZeroEquiv hO hD (polynomialSphereL2 (C 1)) =
      sphereSobolevSingleL 0 0 e := by
    change sphereHarmonicDecomposition hO hD (e : SphereL2) = _
    rw [sphereHarmonicDecomposition_subtype]
    simp [sphereSobolevSingleL,SpectralWeightedGraph.besselWeight]
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  change sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) rho =
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (sphereSobolevSingleL (3/2 : ℝ) 0 e)
  rw [sphereSobolevInclusionL_single]
  rw [← hE,← hw]
  exact (sphereSobolevZeroEquiv hO hD).apply_symm_apply _ |>.symm

theorem sphereSobolev_eq_one_of_native_harmonicPolynomial_reproduces
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (rho : SphereSobolev (3/2 : ℝ))
    (hRep : ∀ p : MvPolynomial (Fin 3) ℝ, AngularPolynomial.laplacian p = 0 →
      sphereSobolevDualPairing (-(1/2 : ℝ))
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) rho))
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (nativeThreeHalfValueTraceL hcalc hF hO hD τ0
            (smoothBallSobolev 2 (smoothPolynomialData p)))) =
          (smoothPolynomialData p).1 0) :
    rho = sphereSobolevSingleL (3/2 : ℝ) 0
      ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩ := by
  apply sphereSobolev_eq_one_of_harmonicPolynomial_reproduces hO hD τ0 rho
  intro p hp
  rw [← nativeThreeHalfTrace_dualPairing_eq_L2_valueTrace hcalc hF hO hD τ0 rho (smoothPolynomialData p)]
  exact hRep p hp

theorem sphereSobolev_eq_one_of_euclideanHarmonic_reproduces
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (rho : SphereSobolev (3/2 : ℝ))
    (hRep : ∀ u : SmoothData,
      (∀ x ∈ (ballOpens : Set R3), GreenRadialTrace.euclideanLaplacian u.1 x = 0) →
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) rho),
        τ0.valueTraceL (smoothSobolev u)⟫_ℝ = u.1 0) :
    rho = sphereSobolevSingleL (3/2 : ℝ) 0
      ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩ := by
  apply sphereSobolev_eq_one_of_harmonicPolynomial_reproduces hO hD τ0 rho
  intro p hp
  apply hRep (smoothPolynomialData p)
  intro x _
  change GreenRadialTrace.euclideanLaplacian (GreenRadialTrace.polynomialEvaluation p) x = 0
  rw [GreenRadialTrace.euclideanLaplacian_polynomialEvaluation,hp]
  simp [GreenRadialTrace.polynomialEvaluation]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
