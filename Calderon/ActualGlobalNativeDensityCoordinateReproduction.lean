import Calderon.ActualGlobalNativeDensityPairedReproduction
import Calderon.PhysicalHarmonicDilation
import Calderon.ActualCoveredScalarTransfer
import Calderon.ActualNormalizedSecondUCPDictionary
import Calderon.ActualKnownSideInteriorSeed
import Calderon.CollaboratorUniqueContinuationProofOct17
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

/-- Scalar linearity of the divergence-form operator in a globally smooth test:
`div(A∇(c f)) = c div(A∇f)`, with globally smooth coefficient entries. -/
theorem coordinateReproduction_divCoeffGrad_const_mul
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => A z i j))
    (c : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    divCoeffGrad A (fun z => c * f z) x = c * divCoeffGrad A f x := by
  have hfd : ∀ z : R3, DifferentiableAt ℝ f z := fun z => hf.differentiable (by simp) z
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  -- Each outer flux row is differentiable at `x`.
  have hrow : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun z => ∑ j : Fin 3, A z i j * fderiv ℝ f z (EuclideanSpace.single j 1)) x := by
    intro i
    exact DifferentiableAt.fun_sum fun j _ => ((hA i j).differentiable (by simp) x).fun_mul
      ((hD.clm_apply (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))).differentiable
        (by simp) x)
  unfold divCoeffGrad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- The inner first derivatives scale linearly everywhere.
  have hEq : (fun z => ∑ j : Fin 3, A z i j *
      fderiv ℝ (fun w => c * f w) z (EuclideanSpace.single j 1)) =
      fun z => c * ∑ j : Fin 3, A z i j * fderiv ℝ f z (EuclideanSpace.single j 1) := by
    funext z
    rw [fderiv_const_mul (hfd z), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hEq, fderiv_const_mul (hrow i), ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem exists_global_native_density_normalized_paired_and_coordinate_reproduction
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u y =
          nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
            y (referenceRadius delta Rstar p L y) y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        lam • y ∈ S.W → ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u y = u.1 y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 ) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
          (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
          (referenceRadius delta Rstar p L) Psi y = 0 ) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1 ) ∧
      (∀ V : Set R3, IsOpen V → ∀ u : SmoothData,
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
            closedBall (0 : R3) 1 ⊆ V) →
        (∀ x ∈ V, coordinateFluxDivergence
          (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∀ v : SmoothData,
        (∀ y ∈ interior cylinder, coordinateFluxDivergence
          (metricDivergenceFlux (fun z => S.g2 (lam • z)) v.1) y = 0) →
        (∀ y ∈ cylinder, lam • y ∈ S.W → u.1 y = v.1 y) →
        ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u y = v.1 y) ∧
      ∀ k : Fin 3, ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi
          (⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩ : SmoothData) y = y k := by
  -- The SAME paired producer: one `Psi` with all previous fields.
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair⟩ :=
    exists_global_native_density_normalized_paired_reproduction
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair,?_⟩
  intro k
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hdil : ContDiff ℝ ∞ (fun y : R3 => lam • y) :=
    (lam • ContinuousLinearMap.id ℝ R3).contDiff
  have hk : ContDiff ℝ ∞ (fun z : R3 => z k) := (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff
  -- Dilated coordinate harmonicity from the ORIGINAL harmonic coordinates and the existing
  -- physical dilation identity; no admissibility of the dilated metric is assumed.
  have hDilHarm : ∀ g : MatrixField, IsAdmissibleMetric g →
      (∀ x ∈ S.coordinateRoom,
        coordinateFluxDivergence (metricDivergenceFlux g (fun z => z k)) x = 0) →
      ∀ x : R3, lam • x ∈ S.coordinateRoom →
        coordinateFluxDivergence
          (metricDivergenceFlux (fun z => g (lam • z)) (fun z => z k)) x = 0 := by
    intro g hg hHarm x hx
    have hs : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => g (lam • x) i j) :=
      fun i j => (hg.smooth i j).comp hdil
    have hp : ∀ x : R3, (g (lam • x)).PosDef := fun x => hg.posDef (lam • x)
    let A : R3 → Matrix (Fin 3) (Fin 3) ℝ := principalCoefficient (fun y => g (lam • y))
    have hAc : ContDiff ℝ ∞ A := by
      first
      | exact contDiff_principalCoefficient_of_smooth_posDef (fun y => g (lam • y)) hs hp
      | exact NormalCoordinatesFrame.contDiff_principalCoefficient_of_smooth_posDef
          (fun y => g (lam • y)) hs hp
    have hAe : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => A z i j) := by
      intro i j
      first
      | exact contDiff_pi.mp (contDiff_pi.mp hAc i) j
      | exact (LinearMap.toContinuousLinearMap
          (Matrix.entryLinearMap ℝ ℝ i j : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℝ)).contDiff.comp hAc
      | exact (contDiff_apply_apply i j).comp hAc
      | exact ((ContinuousLinearMap.proj (R := ℝ) j).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) i)).contDiff.comp hAc
    -- `(lam • y)_k = lam * y_k`.
    have hScale : (fun y : R3 => (lam • y) k) = fun y => lam * y k := by
      funext y
      first
      | rw [PiLp.smul_apply, smul_eq_mul]
      | simp
    -- Linearity in the scalar test, in the SAME divergence/principal-coefficient convention.
    have hL : coordinateFluxDivergence
        (metricDivergenceFlux (fun y => g (lam • y)) (fun y => lam * y k)) x =
        lam * coordinateFluxDivergence
          (metricDivergenceFlux (fun y => g (lam • y)) (fun y => y k)) x := by
      rw [coordinateFluxDivergence_metric_eq_divCoeffGrad,
        coordinateFluxDivergence_metric_eq_divCoeffGrad]
      exact coordinateReproduction_divCoeffGrad_const_mul A hAe lam (fun z : R3 => z k) hk x
    -- The existing physical dilation identity for the ORIGINAL admissible metric.
    have hDil : coordinateFluxDivergence
        (metricDivergenceFlux (fun y => g (lam • y)) (fun y => lam * y k)) x =
        lam ^ 2 * coordinateFluxDivergence (metricDivergenceFlux g (fun z => z k)) (lam • x) := by
      rw [← hScale]
      exact coordinateFluxDivergence_metricDivergenceFlux_dilation g hg lam
        ⟨fun z : R3 => z k, hk⟩ x
    have h3 : lam * coordinateFluxDivergence
        (metricDivergenceFlux (fun y => g (lam • y)) (fun y => y k)) x =
        lam ^ 2 * coordinateFluxDivergence (metricDivergenceFlux g (fun z => z k)) (lam • x) :=
      hL.symm.trans hDil
    rw [hHarm (lam • x) hx, mul_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_left hlam.ne'
  -- The common open first-test room `V = (lam • ·)⁻¹' S.coordinateRoom`.
  have hVopen : IsOpen ((fun x : R3 => lam • x) ⁻¹' S.coordinateRoom) :=
    S.coordinateRoom_open.preimage hdil.continuous
  -- Every actual closed physical ball lies in `V` by the existing cover.
  have hCover : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
        closedBall (0 : R3) 1 ⊆ (fun x : R3 => lam • x) ⁻¹' S.coordinateRoom := by
    rintro i y hy _ ⟨z,hz,rfl⟩
    exact cover.coordinate_room i lam hLam y hy.2 (referenceRadius delta Rstar p L y)
      (referenceRadius_pos delta Rstar p L y hdelta hRstar) (hRadius y hy.1) z
      (closedBall_subset_closedBall (by norm_num) hz)
  -- The first metric coordinate test is harmonic throughout `V`.
  have hHarm1 : ∀ x ∈ (fun x : R3 => lam • x) ⁻¹' S.coordinateRoom,
      coordinateFluxDivergence
        (metricDivergenceFlux (fun z => S.g1 (lam • z)) (fun z => z k)) x = 0 :=
    fun x hx => hDilHarm S.g1 S.g1_admissible (S.harmonic_coordinates1 k) x hx
  -- Cylinder centers dilate into the coordinate room: the actual mixed kernel `K` places
  -- `(endpoint, y)` in its domain, inside the dilated off-diagonal room.
  have hCenter : ∀ y ∈ cylinder, lam • y ∈ S.coordinateRoom := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    have he0 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : R3) ∈ sphere (0 : R3) 1 := by
      first
      | simp
      | rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single, norm_one]
    obtain ⟨-,hy2,-⟩ := K.domain_room (K.sphere_cover i y ⟨hy,hi⟩ _ he0)
    exact hy2
  -- The second metric coordinate test is harmonic on the cylinder interior.
  have hHarm2 : ∀ y ∈ interior cylinder, coordinateFluxDivergence
      (metricDivergenceFlux (fun z => S.g2 (lam • z)) (fun z => z k)) y = 0 :=
    fun y hy => hDilHarm S.g2 S.g2_admissible (S.harmonic_coordinates2 k) y
      (hCenter y (interior_subset hy))
  -- The SAME producer's universal paired reproduction with `u = v = x_k`.
  intro i y hy
  exact hPair ((fun x : R3 => lam • x) ⁻¹' S.coordinateRoom) hVopen
    ⟨fun z : R3 => z k, hk⟩ hCover hHarm1 ⟨fun z : R3 => z k, hk⟩ hHarm2
    (fun _ _ _ => rfl) i y hy

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
