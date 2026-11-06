import Calderon.MixedKernelConstruction.MixedKernelConstructionC4SupportV015
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

section C4CutoffNative
open MeasureTheory
open scoped ContDiff
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
open ConformalDepth

/-- P5: literal COMM for the native first operator `coordinateFluxDivergence ∘
metricDivergenceFlux (g1(lam ·))`. -/
theorem native_first_cutoff_comm (S : KnownSideSourceData) (lam : ℝ) {chi u : R3 → ℝ}
    (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u) (x : R3) :
    coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) (fun y => chi y * u y)) x =
      chi x * coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x +
        u x * coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) chi) x +
        2 * ∑ i, ∑ j, dilatedFirstPrincipal S lam x i j *
          OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j u x := by
  have ha : ∀ i k, ContDiff ℝ ∞ (fun z => dilatedFirstPrincipal S lam z i k) := fun i k =>
    (contDiff_principalCoefficient_entry S.g1 S.g1_admissible i k).comp
      (contDiff_id.const_smul lam)
  have hs : ∀ i k z, dilatedFirstPrincipal S lam z i k = dilatedFirstPrincipal S lam z k i :=
    fun i k z => by
      have h := (principalCoefficient_posDef S.g1 S.g1_admissible (lam • z)).isHermitian.apply k i
      show principalCoefficient S.g1 (lam • z) i k = principalCoefficient S.g1 (lam • z) k i
      simpa using h
  have hop : ∀ (f : R3 → ℝ) (x : R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) f) x =
        OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) f x :=
    fun f x => by rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
  simp only [hop]
  exact CutoffCommutator.Lop_mul_symm (fun i k z => dilatedFirstPrincipal S lam z i k) ha hs
    hc hu x

/-- P5 with the PDE: for a first-operator solution at `x`, the cutoff residual is exactly the
commutator. -/
theorem native_first_cutoff_residual (S : KnownSideSourceData) (lam : ℝ) {chi u : R3 → ℝ}
    (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u) (x : R3)
    (hpde : coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x = 0) :
    coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) (fun y => chi y * u y)) x =
      u x * coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) chi) x +
        2 * ∑ i, ∑ j, dilatedFirstPrincipal S lam x i j *
          OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j u x := by
  rw [native_first_cutoff_comm S lam hc hu x, hpde, mul_zero, zero_add]

/-- P6: literal COMM for the normalized second operator; `beta = secondOperatorFactor` stays
OUTSIDE the divergence and is never differentiated. -/
theorem native_second_cutoff_comm (S : KnownSideSourceData) (L lam : ℝ) {chi u : R3 → ℝ}
    (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u) (x : R3) :
    normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => chi y * u y) x -
        chi x * normalizedSecondLaplacian S.g1 S.g2 L lam u x =
      secondOperatorFactor S L lam x *
        (u x * OAI.AnisotropicCalderon.Lop
            (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) chi x +
          2 * ∑ i, ∑ j, principalCoefficient (dilatedMetric S.g2 lam) x i j *
            OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j u x) := by
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  have hs : ∀ i k z, principalCoefficient (dilatedMetric S.g2 lam) z i k =
      principalCoefficient (dilatedMetric S.g2 lam) z k i := fun i k z => by
    have h := (principalCoefficient_posDef S.g2 S.g2_admissible (lam • z)).isHermitian.apply k i
    show principalCoefficient S.g2 (lam • z) i k = principalCoefficient S.g2 (lam • z) k i
    simpa using h
  have hop : ∀ (f : R3 → ℝ) (x : R3), normalizedSecondLaplacian S.g1 S.g2 L lam f x =
      secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) f x := fun f x => by
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad]
    rfl
  simp only [hop]
  exact CutoffCommutator.beta_Lop_cutoff_comm
    (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) ha hs hc hu
    (secondOperatorFactor S L lam) x

/-- P6 with the PDE: for a second-operator solution at `x`, the cutoff residual is exactly
`beta` times the commutator. -/
theorem native_second_cutoff_residual (S : KnownSideSourceData) (L lam : ℝ) {chi u : R3 → ℝ}
    (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u) (x : R3)
    (hpde : normalizedSecondLaplacian S.g1 S.g2 L lam u x = 0) :
    normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => chi y * u y) x =
      secondOperatorFactor S L lam x *
        (u x * OAI.AnisotropicCalderon.Lop
            (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) chi x +
          2 * ∑ i, ∑ j, principalCoefficient (dilatedMetric S.g2 lam) x i j *
            OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j u x) := by
  have h := native_second_cutoff_comm S L lam hc hu x
  rw [hpde, mul_zero, sub_zero] at h
  exact h

/-- L3: COMM for `w` smooth ONLY on the open `D`, at points of `D`. -/
theorem local_Lop_mul_symm (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hs : ∀ i j x, a i j x = a j i x)
    {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ} (hc : ContDiff ℝ ∞ chi)
    (hw : ContDiffOn ℝ ∞ w D) {x : R3} (hx : x ∈ D) :
    OAI.AnisotropicCalderon.Lop a (fun y => chi y * w y) x =
      chi x * OAI.AnisotropicCalderon.Lop a w x + w x * OAI.AnisotropicCalderon.Lop a chi x +
        2 * ∑ i, ∑ j, a i j x * OAI.AnisotropicCalderon.pd i chi x *
          OAI.AnisotropicCalderon.pd j w x := by
  obtain ⟨ρ, hρ, -, Θ, hΘ, hEq⟩ := exists_smooth_phase_eqOn_ball hD hw x hx
  have hev : Θ =ᶠ[nhds x] w :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x hρ) fun y hy => hEq hy
  have hev2 : (fun y => chi y * Θ y) =ᶠ[nhds x] fun y => chi y * w y :=
    hev.mono fun y hy => by
      show chi y * Θ y = chi y * w y
      rw [hy]
  have hx0 : Θ x = w x := hEq (Metric.mem_ball_self hρ)
  have hpdj : ∀ j, OAI.AnisotropicCalderon.pd j Θ x = OAI.AnisotropicCalderon.pd j w x :=
    fun j => CutoffCommutator.pd_congr_of_eventuallyEq hev j
  rw [← CutoffCommutator.Lop_congr_of_eventuallyEq a hev2,
    ← CutoffCommutator.Lop_congr_of_eventuallyEq a hev, ← hx0]
  simp only [← hpdj]
  exact CutoffCommutator.Lop_mul_symm a ha hs hc hΘ x

/-- L3-first: literal first-operator cutoff residual for a solution smooth only on `D`. -/
theorem native_first_cutoff_residual_local (S : KnownSideSourceData) (lam : ℝ)
    {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ} (hc : ContDiff ℝ ∞ chi)
    (hw : ContDiffOn ℝ ∞ w D) {x : R3} (hx : x ∈ D)
    (hpde : coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x = 0) :
    coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) (fun y => chi y * w y)) x =
      w x * coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) chi) x +
        2 * ∑ i, ∑ j, dilatedFirstPrincipal S lam x i j *
          OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j w x := by
  have ha : ∀ i k, ContDiff ℝ ∞ (fun z => dilatedFirstPrincipal S lam z i k) := fun i k =>
    (contDiff_principalCoefficient_entry S.g1 S.g1_admissible i k).comp
      (contDiff_id.const_smul lam)
  have hs : ∀ i k z, dilatedFirstPrincipal S lam z i k = dilatedFirstPrincipal S lam z k i :=
    fun i k z => by
      have h := (principalCoefficient_posDef S.g1 S.g1_admissible (lam • z)).isHermitian.apply k i
      show principalCoefficient S.g1 (lam • z) i k = principalCoefficient S.g1 (lam • z) k i
      simpa using h
  have hop : ∀ (f : R3 → ℝ),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) f) x =
        OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) f x :=
    fun f => by rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
  rw [hop] at hpde
  simp only [hop]
  rw [local_Lop_mul_symm (fun i k z => dilatedFirstPrincipal S lam z i k) ha hs hD hc hw hx,
    hpde, mul_zero, zero_add]

/-- L3-second: literal normalized-second cutoff residual for a solution smooth only on `D`;
`beta` is not differentiated. -/
theorem native_second_cutoff_residual_local (S : KnownSideSourceData) (L lam : ℝ)
    {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ} (hc : ContDiff ℝ ∞ chi)
    (hw : ContDiffOn ℝ ∞ w D) {x : R3} (hx : x ∈ D)
    (hpde : normalizedSecondLaplacian S.g1 S.g2 L lam w x = 0) :
    normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => chi y * w y) x =
      secondOperatorFactor S L lam x *
        (w x * OAI.AnisotropicCalderon.Lop
            (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) chi x +
          2 * ∑ i, ∑ j, principalCoefficient (dilatedMetric S.g2 lam) x i j *
            OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j w x) := by
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  have hs : ∀ i k z, principalCoefficient (dilatedMetric S.g2 lam) z i k =
      principalCoefficient (dilatedMetric S.g2 lam) z k i := fun i k z => by
    have h := (principalCoefficient_posDef S.g2 S.g2_admissible (lam • z)).isHermitian.apply k i
    show principalCoefficient S.g2 (lam • z) i k = principalCoefficient S.g2 (lam • z) k i
    simpa using h
  have hop : ∀ (f : R3 → ℝ), normalizedSecondLaplacian S.g1 S.g2 L lam f x =
      secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) f x := fun f => by
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad]
    rfl
  rw [hop] at hpde
  have hL : OAI.AnisotropicCalderon.Lop
      (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) w x = 0 :=
    (mul_eq_zero.mp hpde).resolve_left (secondOperatorFactor_pos S L lam x).ne'
  rw [hop, local_Lop_mul_symm (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k)
    ha hs hD hc hw hx, hL, mul_zero, zero_add]

/-- NC1: native first-operator Caccioppoli for a compact cutoff `eta`: ONE constant before
every smooth solution `u` of the LITERAL first PDE on `{eta ≠ 0}`. -/
theorem native_first_caccioppoli (S : KnownSideSourceData) (lam : ℝ) {eta : R3 → ℝ}
    (heta : ContDiff ℝ ∞ eta) (hetac : HasCompactSupport eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : R3 → ℝ, ContDiff ℝ ∞ u →
      (∀ x, eta x ≠ 0 →
        coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x = 0) →
      ∫ x, eta x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i u x ^ 2 ≤
        C * ∫ x, u x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i eta x ^ 2 := by
  have ha : ∀ i k, ContDiff ℝ ∞ (fun z => dilatedFirstPrincipal S lam z i k) := fun i k =>
    (contDiff_principalCoefficient_entry S.g1 S.g1_admissible i k).comp
      (contDiff_id.const_smul lam)
  obtain ⟨C, hC, hcac⟩ := CutoffCommutator.exists_caccioppoli_constant ha heta hetac
    (fun x _ ξ hξ => CutoffCommutator.quadSum_pos_of_posDef
      (principalCoefficient_posDef S.g1 S.g1_admissible (lam • x)) hξ)
  refine ⟨C, hC, fun u hu hpde => hcac u hu fun x hx => ?_⟩
  have hop : coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x =
      OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) u x := by
    rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
  rw [← hop]
  exact hpde x hx

/-- NC2: native normalized-second-operator Caccioppoli; the positive factor `beta` is cancelled
pointwise, never differentiated. -/
theorem native_second_caccioppoli (S : KnownSideSourceData) (L lam : ℝ) {eta : R3 → ℝ}
    (heta : ContDiff ℝ ∞ eta) (hetac : HasCompactSupport eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : R3 → ℝ, ContDiff ℝ ∞ u →
      (∀ x, eta x ≠ 0 → normalizedSecondLaplacian S.g1 S.g2 L lam u x = 0) →
      ∫ x, eta x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i u x ^ 2 ≤
        C * ∫ x, u x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i eta x ^ 2 := by
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  obtain ⟨C, hC, hcac⟩ := CutoffCommutator.exists_caccioppoli_constant ha heta hetac
    (fun x _ ξ hξ => CutoffCommutator.quadSum_pos_of_posDef
      (principalCoefficient_posDef S.g2 S.g2_admissible (lam • x)) hξ)
  refine ⟨C, hC, fun u hu hpde => hcac u hu fun x hx => ?_⟩
  have hop : normalizedSecondLaplacian S.g1 S.g2 L lam u x =
      secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) u x := by
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad]
    rfl
  have hb := hpde x hx
  rw [hop] at hb
  exact (mul_eq_zero.mp hb).resolve_left (secondOperatorFactor_pos S L lam x).ne'

/-- L3-first: native first-operator LOCAL Caccioppoli. `w` is smooth only on the open `D` and
solves the literal first PDE on `tsupport eta ⊆ D`; `C` is chosen before `w`. -/
theorem native_first_local_caccioppoli (S : KnownSideSourceData) (lam : ℝ) {D : Set R3}
    (hD : IsOpen D) {eta : R3 → ℝ} (heta : ContDiff ℝ ∞ eta) (hetac : HasCompactSupport eta)
    (hKD : tsupport eta ⊆ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ tsupport eta,
        coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x = 0) →
      ∫ x, eta x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i w x ^ 2 ≤
        C * ∫ x, w x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i eta x ^ 2 := by
  have ha : ∀ i k, ContDiff ℝ ∞ (fun z => dilatedFirstPrincipal S lam z i k) := fun i k =>
    (contDiff_principalCoefficient_entry S.g1 S.g1_admissible i k).comp
      (contDiff_id.const_smul lam)
  obtain ⟨C, hC, hcac⟩ := CutoffCommutator.exists_local_caccioppoli_constant hD ha heta hetac hKD
    (fun x _ ξ hξ => CutoffCommutator.quadSum_pos_of_posDef
      (principalCoefficient_posDef S.g1 S.g1_admissible (lam • x)) hξ)
  refine ⟨C, hC, fun w hw hpde => hcac w hw fun x hx => ?_⟩
  have hop : coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x =
      OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) w x := by
    rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
  rw [← hop]
  exact hpde x hx

/-- L3-second: native normalized-second LOCAL Caccioppoli; `beta` cancelled pointwise. -/
theorem native_second_local_caccioppoli (S : KnownSideSourceData) (L lam : ℝ) {D : Set R3}
    (hD : IsOpen D) {eta : R3 → ℝ} (heta : ContDiff ℝ ∞ eta) (hetac : HasCompactSupport eta)
    (hKD : tsupport eta ⊆ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ tsupport eta, normalizedSecondLaplacian S.g1 S.g2 L lam w x = 0) →
      ∫ x, eta x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i w x ^ 2 ≤
        C * ∫ x, w x ^ 2 * ∑ i, OAI.AnisotropicCalderon.pd i eta x ^ 2 := by
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  obtain ⟨C, hC, hcac⟩ := CutoffCommutator.exists_local_caccioppoli_constant hD ha heta hetac hKD
    (fun x _ ξ hξ => CutoffCommutator.quadSum_pos_of_posDef
      (principalCoefficient_posDef S.g2 S.g2_admissible (lam • x)) hξ)
  refine ⟨C, hC, fun w hw hpde => hcac w hw fun x hx => ?_⟩
  have hop : normalizedSecondLaplacian S.g1 S.g2 L lam w x =
      secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) w x := by
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad]
    rfl
  have hb := hpde x hx
  rw [hop] at hb
  exact (mul_eq_zero.mp hb).resolve_left (secondOperatorFactor_pos S L lam x).ne'

/-- Z2-first: GLOBAL literal first-operator cutoff residual for `w` smooth and harmonic only on
open `D ⊇ tsupport chi`; outside `D` both sides vanish. -/
theorem native_first_cutoff_residual_global (S : KnownSideSourceData) (lam : ℝ)
    {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ} (hc : ContDiff ℝ ∞ chi)
    (hsub : tsupport chi ⊆ D) (hw : ContDiffOn ℝ ∞ w D)
    (hpde : ∀ x ∈ D,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x = 0)
    (x : R3) :
    coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) (fun y => chi y * w y)) x =
      w x * coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) chi) x +
        2 * ∑ i, ∑ j, dilatedFirstPrincipal S lam x i j *
          OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j w x := by
  by_cases hx : x ∈ D
  · exact native_first_cutoff_residual_local S lam hD hc hw hx (hpde x hx)
  · have hx' : x ∉ tsupport chi := fun h => hx (hsub h)
    have hop : ∀ (f : R3 → ℝ),
        coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) f) x =
          OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) f x :=
      fun f => by rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
    simp only [hop, CutoffCommutator.Lop_mul_eq_zero_of_not_mem_tsupport _ w hx',
      CutoffCommutator.Lop_eq_zero_of_not_mem_tsupport _ hx',
      CutoffCommutator.pd_eq_zero_of_not_mem_tsupport hx']
    simp

/-- Z2-second: GLOBAL literal normalized-second cutoff residual; `beta` stays outside. -/
theorem native_second_cutoff_residual_global (S : KnownSideSourceData) (L lam : ℝ)
    {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ} (hc : ContDiff ℝ ∞ chi)
    (hsub : tsupport chi ⊆ D) (hw : ContDiffOn ℝ ∞ w D)
    (hpde : ∀ x ∈ D, normalizedSecondLaplacian S.g1 S.g2 L lam w x = 0) (x : R3) :
    normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => chi y * w y) x =
      secondOperatorFactor S L lam x *
        (w x * OAI.AnisotropicCalderon.Lop
            (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) chi x +
          2 * ∑ i, ∑ j, principalCoefficient (dilatedMetric S.g2 lam) x i j *
            OAI.AnisotropicCalderon.pd i chi x * OAI.AnisotropicCalderon.pd j w x) := by
  by_cases hx : x ∈ D
  · exact native_second_cutoff_residual_local S L lam hD hc hw hx (hpde x hx)
  · have hx' : x ∉ tsupport chi := fun h => hx (hsub h)
    have hop : normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => chi y * w y) x =
        secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop
          (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k)
          (fun y => chi y * w y) x := by
      rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv,
        coordinateFluxDivergence_eq_divCoeffGrad]
      rfl
    rw [hop, CutoffCommutator.Lop_mul_eq_zero_of_not_mem_tsupport _ w hx',
      CutoffCommutator.Lop_eq_zero_of_not_mem_tsupport _ hx']
    simp [CutoffCommutator.pd_eq_zero_of_not_mem_tsupport hx']

/-- Z3-first: the global first residual vanishes off the TRANSITION set
`tsupport chi ∩ {x | chi is not locally constant at x}`. -/
theorem native_first_cutoff_residual_eq_zero (S : KnownSideSourceData) (lam : ℝ)
    {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ} (hc : ContDiff ℝ ∞ chi)
    (hsub : tsupport chi ⊆ D) (hw : ContDiffOn ℝ ∞ w D)
    (hpde : ∀ x ∈ D,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x = 0)
    {x : R3} {c : ℝ} (hconst : chi =ᶠ[nhds x] fun _ => c) :
    coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) (fun y => chi y * w y)) x = 0 := by
  have hop : coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) chi) x =
      OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) chi x := by
    rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
  rw [native_first_cutoff_residual_global S lam hD hc hsub hw hpde x, hop,
    CutoffCommutator.Lop_eq_zero_of_eventuallyEq_const _ hconst]
  simp [CutoffCommutator.pd_eq_zero_of_eventuallyEq_const hconst]

/-- Z3-second: the global normalized-second residual vanishes off the transition set. -/
theorem native_second_cutoff_residual_eq_zero (S : KnownSideSourceData) (L lam : ℝ)
    {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ} (hc : ContDiff ℝ ∞ chi)
    (hsub : tsupport chi ⊆ D) (hw : ContDiffOn ℝ ∞ w D)
    (hpde : ∀ x ∈ D, normalizedSecondLaplacian S.g1 S.g2 L lam w x = 0)
    {x : R3} {c : ℝ} (hconst : chi =ᶠ[nhds x] fun _ => c) :
    normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => chi y * w y) x = 0 := by
  rw [native_second_cutoff_residual_global S L lam hD hc hsub hw hpde x,
    CutoffCommutator.Lop_eq_zero_of_eventuallyEq_const _ hconst]
  simp [CutoffCommutator.pd_eq_zero_of_eventuallyEq_const hconst]

end C4CutoffNative

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
