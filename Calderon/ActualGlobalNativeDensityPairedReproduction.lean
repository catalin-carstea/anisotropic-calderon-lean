import Calderon.ActualGlobalNativeDensityNormalization
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

/-- Local linearity of the divergence-form operator: on an open set where both functions are
smooth (and the coefficient entries are globally smooth), `div(A∇(f-g)) = div(A∇f) - div(A∇g)`.
Only smoothness on the open set `U` is used; no global regularity of `f` or `g` is assumed. -/
theorem pairedReproduction_divCoeffGrad_sub_of_isOpen
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => A z i j))
    (U : Set R3) (hU : IsOpen U) (f g : R3 → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (x : R3) (hx : x ∈ U) :
    divCoeffGrad A (fun z => f z - g z) x = divCoeffGrad A f x - divCoeffGrad A g x := by
  have hfd : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hgd : ∀ z ∈ U, DifferentiableAt ℝ g z := fun z hz =>
    (hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  -- Each outer flux row is differentiable at `x`, using second derivatives only inside `U`.
  have hrow : ∀ h : R3 → ℝ, ContDiffOn ℝ ∞ h U → ∀ i : Fin 3, DifferentiableAt ℝ
      (fun z => ∑ j : Fin 3, A z i j * fderiv ℝ h z (EuclideanSpace.single j 1)) x := by
    intro h hh i
    have hD : ContDiffAt ℝ ∞ (fderiv ℝ h) x :=
      (hh.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp)
    exact DifferentiableAt.fun_sum fun j _ => ((hA i j).differentiable (by simp) x).fun_mul
      ((hD.clm_apply (contDiffAt_const (c := EuclideanSpace.single j (1 : ℝ)))).differentiableAt
        (by simp))
  unfold divCoeffGrad
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  -- The inner first derivatives split linearly on the open neighbourhood `U` of `x`.
  have hEv : (fun z => ∑ j : Fin 3, A z i j *
      fderiv ℝ (fun w => f w - g w) z (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      fun z => (∑ j : Fin 3, A z i j * fderiv ℝ f z (EuclideanSpace.single j 1)) -
        ∑ j : Fin 3, A z i j * fderiv ℝ g z (EuclideanSpace.single j 1) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    rw [fderiv_fun_sub (hfd z hz) (hgd z hz), ← Finset.sum_sub_distrib]
    simp only [ContinuousLinearMap.sub_apply, mul_sub]
  rw [hEv.fderiv_eq, fderiv_fun_sub (hrow f hf i) (hrow g hg i),
    ContinuousLinearMap.sub_apply]

theorem exists_global_native_density_normalized_paired_reproduction
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
      ∀ V : Set R3, IsOpen V → ∀ u : SmoothData,
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
            lam delta Rstar p Psi u y = v.1 y := by
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass⟩ :=
    exists_global_native_density_operator_and_constant_normalization
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,?_⟩
  intro V hV u hCover hPhys v hHarm hMatch
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  -- Step 1: the actual covered scalar gluing, with local PDE input from the SAME producer.
  obtain ⟨F,hFeq,hFcont,hFsmooth,hFpde⟩ :=
    exists_native_covered_scalar_function_of_local_secondPDE hO hD τ0 S L lam delta Rstar p
      cover hdelta hRstar hLam hRadius Psi u
      (fun i y hy => hPDE i y hy V hV u (hCover i y hy) hPhys)
  -- Step 2: on the original known side, `F = u = v`.
  have hKnownF : ∀ y ∈ cylinder, lam • y ∈ S.W → F y = v.1 y := by
    intro y hy hW
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0 := by
      intro z hz
      have hzBall : z ∈ ball (0 : R3) 1 := by
        simpa only [coe_ballOpens,B] using hz
      exact hPhys _ (hCover i y ⟨hy,hi⟩ ⟨z,ball_subset_closedBall hzBall,rfl⟩)
    rw [hFeq i y ⟨hy,hi⟩, hKnown i y ⟨hy,hi⟩ hW u hBall]
    exact hMatch y hy hW
  -- Step 3: the actual dilated second-metric principal coefficient (original `g2` composed).
  let A : R3 → Matrix (Fin 3) (Fin 3) ℝ := principalCoefficient (fun y => S.g2 (lam • y))
  have hdil : ContDiff ℝ ∞ (fun y : R3 => lam • y) :=
    (lam • ContinuousLinearMap.id ℝ R3).contDiff
  have hs : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => S.g2 (lam • x) i j) :=
    fun i j => (S.g2_admissible.smooth i j).comp hdil
  have hp : ∀ x : R3, (S.g2 (lam • x)).PosDef := fun x => S.g2_admissible.posDef (lam • x)
  have hAc : ContDiff ℝ ∞ A := by
    first
    | exact contDiff_principalCoefficient_of_smooth_posDef (fun y => S.g2 (lam • y)) hs hp
    | exact NormalCoordinatesFrame.contDiff_principalCoefficient_of_smooth_posDef
        (fun y => S.g2 (lam • y)) hs hp
  have hApos : ∀ x : R3, (A x).PosDef := by
    intro x
    have hv : 0 < vol (fun y => S.g2 (lam • y)) x := by
      first
      | exact vol_pos_of_posDef (fun y => S.g2 (lam • y)) hp x
      | exact AngularPolynomial.vol_pos_of_posDef (fun y => S.g2 (lam • y)) hp x
      | exact vol_pos_of_posDef _ (dilatedMetric_posDef S.g2 S.g2_admissible lam) x
      | exact AngularPolynomial.vol_pos_of_posDef _
          (dilatedMetric_posDef S.g2 S.g2_admissible lam) x
    exact (hp x).inv.smul hv
  have hAe : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => A z i j) := by
    intro i j
    first
    | exact contDiff_pi.mp (contDiff_pi.mp hAc i) j
    | exact (LinearMap.toContinuousLinearMap
        (Matrix.entryLinearMap ℝ ℝ i j : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℝ)).contDiff.comp hAc
    | exact (contDiff_apply_apply i j).comp hAc
    | exact ((ContinuousLinearMap.proj (R := ℝ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℝ) i)).contDiff.comp hAc
  -- Checked dictionaries: both `F` and `v` solve `div(A∇·) = 0` on the interior.
  have hFdiv : ∀ y ∈ interior cylinder, divCoeffGrad A F y = 0 := fun y hy =>
    (normalizedSecondLaplacian_eq_zero_iff_divCoeffGrad S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam F y).1 (hFpde y hy)
  have hvdiv : ∀ y ∈ interior cylinder, divCoeffGrad A v.1 y = 0 := fun y hy =>
    (coordinateFluxDivergence_metric_eq_divCoeffGrad (fun z => S.g2 (lam • z)) v.1 y).symm.trans
      (hHarm y hy)
  -- The open cylinder: open, star-convex about the origin, inside the interior.
  let D : Set R3 := {z | z 0 ^ 2 + z 1 ^ 2 < 1 ∧ (-1 : ℝ) < z 2 ∧ z 2 < 1}
  have hc (k : Fin 3) : Continuous (fun z : R3 => z k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
  have hDopen : IsOpen D := (isOpen_lt ((hc 0).pow 2 |>.add ((hc 1).pow 2))
      continuous_const).inter
    ((isOpen_lt continuous_const (hc 2)).inter (isOpen_lt (hc 2) continuous_const))
  have hDcyl : D ⊆ cylinder := by
    rintro z ⟨hxy,hlo,hhi⟩
    exact ⟨hxy.le,hlo.le,hhi.le⟩
  have hDint : D ⊆ interior cylinder := interior_maximal hDcyl hDopen
  have h0D : (0 : R3) ∈ D := by norm_num [D]
  have hStar : StarConvex ℝ (0 : R3) D := by
    intro y hy a b ha hb hab
    rw [smul_zero,zero_add]
    rcases (show b ≤ 1 by linarith).lt_or_eq with hb1 | hb1
    · exact constantNormalization_smul_mem_open_cylinder (hDcyl hy) hb hb1
    · rw [hb1,one_smul]
      exact hy
  have hDconn : IsConnected D := (hStar.isPathConnected h0D).isConnected
  -- Step 4: the genuinely local subtraction on the open room `D` (F is smooth only there).
  have hFD : ContDiffOn ℝ ∞ F D := hFsmooth.mono hDint
  have hvD : ContDiffOn ℝ ∞ v.1 D := v.2.contDiffOn
  have hdiff : ∀ x ∈ D, divCoeffGrad A (fun z => F z - v.1 z) x = 0 := by
    intro x hx
    rw [pairedReproduction_divCoeffGrad_sub_of_isOpen A hAe D hDopen F v.1 hFD hvD x hx,
      hFdiv x (hDint hx), hvdiv x (hDint hx), sub_self]
  -- Step 5: the actual nonempty open known-side seed and the EXISTING proved UCP.
  let W0 : Set R3 := D ∩ (fun y : R3 => lam • y) ⁻¹' S.W
  have hW0open : IsOpen W0 := hDopen.inter (S.W_open.preimage hdil.continuous)
  have hW0ne : W0.Nonempty :=
    known_side_seed_nonempty_in_open_neighborhood S lam hlam D hDopen h0D
  have hW0zero : ∀ x ∈ W0, (fun z => F z - v.1 z) x = 0 := by
    intro x hx
    show F x - v.1 x = 0
    rw [hKnownF x (hDcyl hx.1) hx.2, sub_self]
  have hUCP := uniqueContinuation D hDopen hDconn A hAc.contDiffOn (fun x _ => hApos x)
    (fun z => F z - v.1 z) (hFD.sub hvD) hdiff W0 hW0open hW0ne inter_subset_left hW0zero
  have hEqD : ∀ y ∈ D, F y = v.1 y := by
    intro y hy
    have h : F y - v.1 y = 0 := hUCP y hy
    linarith
  -- Step 6: relative-continuous radial limits to the ENTIRE closed cylinder (corners included).
  have hAll : ∀ y ∈ cylinder, F y = v.1 y := by
    intro y hy
    have hT0 : Tendsto (fun s : ℝ => s • y) (𝓝 1) (𝓝 ((1 : ℝ) • y)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at hT0
    have hT : Tendsto (fun s : ℝ => s • y) (𝓝[<] (1 : ℝ)) (𝓝 y) :=
      hT0.mono_left nhdsWithin_le_nhds
    have hIn : ∀ᶠ s in 𝓝[<] (1 : ℝ), s • y ∈ cylinder := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact hDcyl (constantNormalization_smul_mem_open_cylinder hy hs.1.le hs.2)
    have hTc : Tendsto (fun s : ℝ => s • y) (𝓝[<] (1 : ℝ)) (𝓝[cylinder] y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hT,hIn⟩
    have hFT : Tendsto (fun s : ℝ => F (s • y)) (𝓝[<] (1 : ℝ)) (𝓝 (F y)) :=
      (hFcont y hy).tendsto.comp hTc
    have hvT : Tendsto (fun s : ℝ => v.1 (s • y)) (𝓝[<] (1 : ℝ)) (𝓝 (v.1 y)) :=
      (v.2.continuous.tendsto y).comp hT
    have hEv : ∀ᶠ s in 𝓝[<] (1 : ℝ), F (s • y) = v.1 (s • y) := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact hEqD _ (constantNormalization_smul_mem_open_cylinder hy hs.1.le hs.2)
    have hEq : (fun s : ℝ => v.1 (s • y)) =ᶠ[𝓝[<] (1 : ℝ)] (fun s : ℝ => F (s • y)) :=
      hEv.mono fun s hs => hs.symm
    exact tendsto_nhds_unique hFT (hvT.congr' hEq)
  intro i y hy
  exact (hFeq i y hy).symm.trans (hAll y hy.1)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
