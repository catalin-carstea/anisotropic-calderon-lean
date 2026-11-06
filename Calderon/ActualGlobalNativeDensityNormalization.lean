import Calderon.ActualGlobalNativeDensityOperatorPackage
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

/-- The divergence-form operator annihilates the constant one function. -/
theorem constantNormalization_divCoeffGrad_const_one
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (x : R3) :
    divCoeffGrad A (fun _ : R3 => (1 : ℝ)) x = 0 := by
  unfold divCoeffGrad
  first
  | (simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, mul_zero,
      Finset.sum_const_zero]; done)
  | simp

/-- Subtracting a constant does not change the divergence-form operator. -/
theorem constantNormalization_divCoeffGrad_sub_const
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) (c : ℝ) (x : R3) :
    divCoeffGrad A (fun z => u z - c) x = divCoeffGrad A u x := by
  unfold divCoeffGrad
  simp only [fderiv_sub_const]

/-- Radial interpolation `s • y` with `0 ≤ s < 1` of a closed-cylinder point lies in the
open cylinder. -/
theorem constantNormalization_smul_mem_open_cylinder
    {y : R3} (hy : y ∈ cylinder) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    s • y ∈ {z : R3 | z 0 ^ 2 + z 1 ^ 2 < 1 ∧ (-1 : ℝ) < z 2 ∧ z 2 < 1} := by
  obtain ⟨hxy,hlo,hhi⟩ := hy
  have hc : ∀ i : Fin 3, (s • y) i = s * y i := fun i => by simp
  simp only [mem_setOf_eq, hc]
  have hs2 : s ^ 2 < 1 := by nlinarith
  refine ⟨?_,?_,?_⟩
  · nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 hxy)]
  · nlinarith [mul_nonneg hs0 (show (0 : ℝ) ≤ y 2 + 1 by linarith)]
  · nlinarith [mul_nonneg hs0 (show (0 : ℝ) ≤ 1 - y 2 by linarith)]

theorem exists_global_native_density_operator_and_constant_normalization
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
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1 := by
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator⟩ :=
    exists_global_native_density_reproduction_and_operator_equation
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,?_⟩
  let one : SmoothData := ⟨fun _ => (1 : ℝ),contDiff_const⟩
  -- One packet fixes the single scalar functional of the constant datum.
  let i0 : Fin cover.count := ⟨0,cover.count_positive⟩
  let f : R3 → ℝ :=
    nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i0) lam delta Rstar p Psi one
  -- The physical pullback of the constant datum is the same constant datum for every packet.
  have hIndep : ∀ i : Fin cover.count,
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi one = f := by
    intro i
    funext y
    first
    | rfl
    | (unfold nativeMixedKernelDensityFunctional; rfl)
    | (simp only [f, nativeMixedKernelDensityFunctional, referencePhysicalPullbackData])
  -- The constant datum solves the physical first-metric equation everywhere.
  have hphys : ∀ x : R3, coordinateFluxDivergence
      (metricDivergenceFlux (fun z => S.g1 (lam • z)) one.1) x = 0 := by
    intro x
    rw [coordinateFluxDivergence_metric_eq_divCoeffGrad]
    exact constantNormalization_divCoeffGrad_const_one _ x
  -- The actual dilated second-metric principal coefficient.
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
  -- Local smoothness and the dilated second-metric equation at every closed-cylinder point.
  have hloc : ∀ y ∈ cylinder, ContDiffAt ℝ ∞ f y ∧ divCoeffGrad A f y = 0 := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    obtain ⟨Y,hY,hyY,hSmooth,hZero⟩ :=
      hPDE i y ⟨hy,hi⟩ univ isOpen_univ one (subset_univ _) (fun x _ => hphys x)
    rw [hIndep i] at hSmooth hZero
    exact ⟨hSmooth.contDiffAt (hY.mem_nhds hyY),
      (normalizedSecondLaplacian_eq_zero_iff_divCoeffGrad S.g1 S.g2 S.g1_admissible
        S.g2_admissible L lam f y).1 (hZero y hyY)⟩
  -- The open cylinder: open, star-convex about the origin, inside the closed cylinder.
  let D : Set R3 := {z | z 0 ^ 2 + z 1 ^ 2 < 1 ∧ (-1 : ℝ) < z 2 ∧ z 2 < 1}
  have hc (k : Fin 3) : Continuous (fun z : R3 => z k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
  have hDopen : IsOpen D := (isOpen_lt ((hc 0).pow 2 |>.add ((hc 1).pow 2))
      continuous_const).inter
    ((isOpen_lt continuous_const (hc 2)).inter (isOpen_lt (hc 2) continuous_const))
  have hDcyl : D ⊆ cylinder := by
    rintro z ⟨hxy,hlo,hhi⟩
    exact ⟨hxy.le,hlo.le,hhi.le⟩
  have h0D : (0 : R3) ∈ D := by norm_num [D]
  have hStar : StarConvex ℝ (0 : R3) D := by
    intro y hy a b ha hb hab
    rw [smul_zero,zero_add]
    rcases (show b ≤ 1 by linarith).lt_or_eq with hb1 | hb1
    · exact constantNormalization_smul_mem_open_cylinder (hDcyl hy) hb hb1
    · rw [hb1,one_smul]
      exact hy
  have hDconn : IsConnected D := (hStar.isPathConnected h0D).isConnected
  -- The actual nonempty open known-side seed inside the open cylinder.
  let V : Set R3 := D ∩ (fun y : R3 => lam • y) ⁻¹' S.W
  have hVopen : IsOpen V := hDopen.inter (S.W_open.preimage hdil.continuous)
  have hVne : V.Nonempty := known_side_seed_nonempty_in_open_neighborhood S lam hlam D hDopen h0D
  have hVzero : ∀ x ∈ V, (fun z => f z - 1) x = 0 := by
    intro x hx
    obtain ⟨i,hi⟩ := cover.covers_cylinder x (hDcyl hx.1)
    have h := hKnown i x ⟨hDcyl hx.1,hi⟩ hx.2 one (fun z _ => hphys _)
    rw [hIndep i] at h
    have h' : f x = 1 := h
    show f x - 1 = 0
    rw [h',sub_self]
  -- The existing proved unique continuation applied to `f - 1` on the open cylinder.
  have hUCP := uniqueContinuation D hDopen hDconn A hAc.contDiffOn (fun x _ => hApos x)
    (fun z => f z - 1)
    (fun x hx => ((hloc x (hDcyl hx)).1.sub contDiffAt_const).contDiffWithinAt)
    (fun x hx => (constantNormalization_divCoeffGrad_sub_const A f 1 x).trans
      (hloc x (hDcyl hx)).2)
    V hVopen hVne inter_subset_left hVzero
  have hNormD : ∀ y ∈ D, f y = 1 := by
    intro y hy
    have h : f y - 1 = 0 := hUCP y hy
    linarith
  -- Extension by continuity along radial limits to the ENTIRE closed cylinder.
  have hNorm : ∀ y ∈ cylinder, f y = 1 := by
    intro y hy
    have hT0 : Tendsto (fun s : ℝ => s • y) (𝓝 1) (𝓝 ((1 : ℝ) • y)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at hT0
    have hT : Tendsto (fun s : ℝ => s • y) (𝓝[<] (1 : ℝ)) (𝓝 y) :=
      hT0.mono_left nhdsWithin_le_nhds
    have hfT : Tendsto (fun s : ℝ => f (s • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) :=
      (hloc y hy).1.continuousAt.tendsto.comp hT
    have hEv : ∀ᶠ s in 𝓝[<] (1 : ℝ), f (s • y) = 1 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact hNormD _ (constantNormalization_smul_mem_open_cylinder hy hs.1.le hs.2)
    have hEq : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝[<] (1 : ℝ)] (fun s : ℝ => f (s • y)) :=
      hEv.mono fun s hs => hs.symm
    exact tendsto_nhds_unique hfT (tendsto_const_nhds.congr' hEq)
  intro i y hy
  exact (congrFun (hIndep i) y).trans (hNorm y hy.1)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
